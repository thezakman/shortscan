package shortscan

import (
	"fmt"
	"net/http"
	nurl "net/url"
	"sort"
	"strconv"
	"strings"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
)

// exactShortAlias is deliberately a basename, not a path. Keeping the input to
// one 8.3 component lets the probe construct same-length controls without
// turning this mode into an arbitrary URL requester.
type exactShortAlias struct {
	Stem      string
	Prefix    string
	Ordinal   string
	Extension string
	Automatic bool
}

func (a exactShortAlias) name() string {
	name := a.Stem
	if a.Extension != "" {
		name += "." + a.Extension
	}
	return name
}

func (a exactShortAlias) tildePart() string {
	if !a.Automatic {
		return ""
	}
	return "~" + a.Ordinal
}

func (a exactShortAlias) filePart() string {
	if a.Automatic {
		return a.Prefix
	}
	return a.Stem
}

func (a exactShortAlias) extensionPart() string {
	if a.Extension == "" {
		return ""
	}
	return "." + a.Extension
}

func (a exactShortAlias) collisionGroup() string {
	if !a.Automatic {
		return ""
	}
	return a.Prefix + "~*" + a.extensionPart()
}

func (a exactShortAlias) customSFNCandidate() bool {
	return !a.Automatic
}

// guardBypassCandidate mirrors the syntactic gate found in
// iiscore!CheckIfShortFileName. It is deliberately only a candidate label:
// remotely seeing an ordinary 8.3-looking URL does not prove that the name is
// alternate NTFS metadata for a different LFN.
func (a exactShortAlias) guardBypassCandidate() bool {
	for index := 0; index+1 < len(a.Stem); index++ {
		if a.Stem[index] == '~' && a.Stem[index+1] >= '0' && a.Stem[index+1] <= '9' {
			return false
		}
	}
	return true
}

func validExactShortChar(c byte) bool {
	if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' {
		return true
	}
	return strings.ContainsRune("$%'_-@`!(){}^#&~", rune(c))
}

func parseExactShortAlias(raw string) (exactShortAlias, error) {
	shortName := strings.TrimSpace(raw)
	if shortName == "" {
		return exactShortAlias{}, fmt.Errorf("alias is empty")
	}
	if strings.ContainsAny(shortName, "/\\:?") {
		return exactShortAlias{}, fmt.Errorf("%q must be a basename, not a path or URL", raw)
	}
	if strings.Count(shortName, ".") > 1 {
		return exactShortAlias{}, fmt.Errorf("%q has more than one extension separator", raw)
	}

	stem, extension, hasExtension := strings.Cut(shortName, ".")
	if hasExtension && extension == "" {
		return exactShortAlias{}, fmt.Errorf("%q has an empty extension", raw)
	}
	if stem == "" || len(stem) > 8 {
		return exactShortAlias{}, fmt.Errorf("%q has an invalid 8.3 stem length", raw)
	}
	if len(extension) > 3 {
		return exactShortAlias{}, fmt.Errorf("%q has an extension longer than three characters", raw)
	}
	for _, part := range []string{stem, extension} {
		for i := range part {
			if !validExactShortChar(part[i]) {
				return exactShortAlias{}, fmt.Errorf("%q contains a character outside the 8.3 probe alphabet", raw)
			}
		}
	}

	alias := exactShortAlias{Stem: strings.ToUpper(stem), Extension: strings.ToUpper(extension)}
	if strings.Count(alias.Stem, "~") == 1 {
		tilde := strings.LastIndexByte(alias.Stem, '~')
		prefix, ordinal := alias.Stem[:tilde], alias.Stem[tilde+1:]
		automatic := prefix != "" && len(prefix) <= 6 && ordinal != "" && ordinal[0] != '0'
		for i := range ordinal {
			automatic = automatic && ordinal[i] >= '0' && ordinal[i] <= '9'
		}
		if automatic {
			alias.Prefix, alias.Ordinal, alias.Automatic = prefix, ordinal, true
		}
	}
	return alias, nil
}

func exactAliasControls(alias exactShortAlias) []exactShortAlias {
	replacements := []byte{'Z', 'Q', 'X', 'V'}
	controls := make([]exactShortAlias, 0, 2)
	position := len(alias.Stem) - 1
	if alias.Automatic {
		position = len(alias.Prefix) - 1
	} else {
		for position >= 0 && alias.Stem[position] == '~' {
			position--
		}
	}
	if position < 0 {
		return controls
	}
	for _, replacement := range replacements {
		last := alias.Stem[position]
		if replacement == last {
			continue
		}
		control := alias
		control.Stem = alias.Stem[:position] + string(replacement) + alias.Stem[position+1:]
		if alias.Automatic {
			control.Prefix = control.Stem[:len(alias.Prefix)]
		}
		duplicate := false
		for _, existing := range controls {
			if existing.name() == control.name() {
				duplicate = true
				break
			}
		}
		if !duplicate {
			controls = append(controls, control)
		}
		if len(controls) == 2 {
			break
		}
	}
	return controls
}

type exactAliasBase struct {
	URL                 string
	Origin              string
	EscapedPath         string
	AppRootEscaped      string
	RelativeEscapedPath string
}

func normalizeExactAliasAppRoot(raw string) (string, error) {
	appRoot := strings.TrimSpace(raw)
	if appRoot == "" {
		appRoot = "/"
	}
	if !strings.HasPrefix(appRoot, "/") || strings.HasPrefix(appRoot, "//") || strings.Contains(appRoot, "\\") {
		return "", fmt.Errorf("must be an absolute URL path such as / or /webform/")
	}
	u, err := nurl.ParseRequestURI(appRoot)
	if err != nil || u.Host != "" || u.Scheme != "" || u.RawQuery != "" || u.ForceQuery || u.Fragment != "" {
		return "", fmt.Errorf("must be a path without a host, query, or fragment")
	}
	for _, segment := range strings.Split(u.Path, "/") {
		if segment == "." || segment == ".." {
			return "", fmt.Errorf("dot segments are not accepted")
		}
	}
	escaped := u.EscapedPath()
	if escaped == "" {
		escaped = "/"
	}
	if !strings.HasSuffix(escaped, "/") {
		escaped += "/"
	}
	return escaped, nil
}

func normalizeExactAliasBase(raw, appRootRaw string) (exactAliasBase, error) {
	value := strings.TrimSpace(raw)
	if !strings.Contains(value, "://") {
		value = "https://" + value
	}
	u, err := nurl.Parse(value)
	if err != nil {
		return exactAliasBase{}, err
	}
	u.Scheme = strings.ToLower(u.Scheme)
	if u.Scheme != "http" && u.Scheme != "https" {
		return exactAliasBase{}, fmt.Errorf("URL scheme must be http or https")
	}
	if u.Host == "" || u.Opaque != "" {
		return exactAliasBase{}, fmt.Errorf("URL must include a host")
	}
	if u.RawQuery != "" || u.ForceQuery || u.Fragment != "" {
		return exactAliasBase{}, fmt.Errorf("URL must identify a directory without query or fragment")
	}
	escapedPath := u.EscapedPath()
	if escapedPath == "" {
		escapedPath = "/"
	}
	if !strings.HasSuffix(escapedPath, "/") {
		escapedPath += "/"
	}
	appRoot, err := normalizeExactAliasAppRoot(appRootRaw)
	if err != nil {
		return exactAliasBase{}, err
	}
	if !strings.HasPrefix(strings.ToLower(escapedPath), strings.ToLower(appRoot)) {
		return exactAliasBase{}, fmt.Errorf("URL path %q is outside application root %q", escapedPath, appRoot)
	}
	originURL := &nurl.URL{Scheme: u.Scheme, User: u.User, Host: u.Host}
	origin := originURL.String()
	return exactAliasBase{
		URL: origin + escapedPath, Origin: origin, EscapedPath: escapedPath,
		AppRootEscaped: appRoot, RelativeEscapedPath: escapedPath[len(appRoot):],
	}, nil
}

type exactAliasRepresentation struct {
	Profile     string
	FirstToken  string
	SecondToken string
	Tilde       string
}

func newExactAliasRepresentation(profile string) (exactAliasRepresentation, error) {
	switch profile {
	case "direct":
		return exactAliasRepresentation{Profile: profile, Tilde: encodeTilde()}, nil
	case "late":
		first, second := sessionPathTokens()
		return exactAliasRepresentation{Profile: profile, FirstToken: first, SecondToken: second, Tilde: encodeTilde()}, nil
	case "late-encoded":
		token := sessionToken()
		return exactAliasRepresentation{
			Profile: profile, FirstToken: encodeOuterSessionParentheses(token),
			SecondToken: percentEncodeSessionToken(token), Tilde: "%7E",
		}, nil
	default:
		return exactAliasRepresentation{}, fmt.Errorf("unknown exact-short profile %q", profile)
	}
}

func buildExactAliasProbeURL(base exactAliasBase, alias exactShortAlias, representation exactAliasRepresentation) string {
	if representation.Profile == "direct" {
		parts := strings.Split(alias.Stem, "~")
		for index := range parts {
			parts[index] = nurl.PathEscape(parts[index])
		}
		name := strings.Join(parts, representation.Tilde)
		if alias.Extension != "" {
			name += "." + nurl.PathEscape(alias.Extension)
		}
		return base.Origin + base.EscapedPath + name
	}
	prefix := nurl.PathEscape(alias.Prefix)
	suffix := representation.Tilde + alias.Ordinal
	if alias.Extension != "" {
		suffix += "." + nurl.PathEscape(alias.Extension)
	}
	// The native stage consumes the first standalone modifier. The managed
	// stage can then remove the second modifier and join PREFIX with ~N. The
	// exact alias therefore does not exist in the raw path received on the wire.
	return base.Origin + base.AppRootEscaped + representation.FirstToken + "/" +
		base.RelativeEscapedPath + prefix + "/" +
		representation.SecondToken + suffix
}

type exactAliasSignature struct {
	Status        int
	ContentLength int64
	ContentType   string
	Allow         string
	ETag          string
	AspNetVersion string
	MVCVersion    string
}

func normalizeHeaderSet(value string) string {
	if strings.TrimSpace(value) == "" {
		return ""
	}
	parts := strings.Split(value, ",")
	for i := range parts {
		parts[i] = strings.ToLower(strings.TrimSpace(parts[i]))
	}
	sort.Strings(parts)
	return strings.Join(parts, ",")
}

func exactAliasSignatureFromResponse(res *http.Response) exactAliasSignature {
	return exactAliasSignature{
		Status:        res.StatusCode,
		ContentLength: res.ContentLength,
		ContentType:   strings.ToLower(strings.TrimSpace(res.Header.Get("Content-Type"))),
		Allow:         normalizeHeaderSet(res.Header.Get("Allow")),
		ETag:          strings.TrimSpace(res.Header.Get("ETag")),
		AspNetVersion: strings.TrimSpace(res.Header.Get("X-AspNet-Version")),
		MVCVersion:    strings.TrimSpace(res.Header.Get("X-AspNetMvc-Version")),
	}
}

func (s exactAliasSignature) compact() string {
	return "status=" + strconv.Itoa(s.Status) +
		",length=" + strconv.FormatInt(s.ContentLength, 10) +
		",type=" + strconv.Quote(s.ContentType) +
		",allow=" + strconv.Quote(s.Allow) +
		",etag=" + strconv.Quote(s.ETag) +
		",aspnet=" + strconv.Quote(s.AspNetVersion) +
		",mvc=" + strconv.Quote(s.MVCVersion)
}

func (s exactAliasSignature) transient() bool {
	return s.Status == http.StatusRequestTimeout || s.Status == http.StatusTooEarly ||
		s.Status == http.StatusTooManyRequests || s.Status >= 500
}

type exactAliasObservation struct {
	Profile      string
	Method       string
	CandidateURL string
	ControlURLs  []string
	Candidate    exactAliasSignature
	Control      exactAliasSignature
	Repeats      int
	Stable       bool
	Differential bool
	Reason       string
}

func signaturesStable(signatures []exactAliasSignature) (exactAliasSignature, bool) {
	if len(signatures) == 0 {
		return exactAliasSignature{}, false
	}
	first := signatures[0]
	for _, signature := range signatures[1:] {
		if signature != first {
			return first, false
		}
	}
	return first, true
}

func probeExactAliasProfile(hc *http.Client, st *httpStats, base exactAliasBase, alias exactShortAlias, profile, method string, repeats int) (exactAliasObservation, error) {
	if !alias.Automatic && profile != "direct" {
		return exactAliasObservation{}, fmt.Errorf("custom 8.3 candidate %q supports only the direct profile", alias.name())
	}
	representation, err := newExactAliasRepresentation(profile)
	if err != nil {
		return exactAliasObservation{}, err
	}
	controls := exactAliasControls(alias)
	if len(controls) != 2 {
		return exactAliasObservation{}, fmt.Errorf("unable to construct two controls for %q", alias.name())
	}
	observation := exactAliasObservation{Profile: profile, Method: method, Repeats: repeats}
	observation.CandidateURL = buildExactAliasProbeURL(base, alias, representation)
	for _, control := range controls {
		observation.ControlURLs = append(observation.ControlURLs, buildExactAliasProbeURL(base, control, representation))
	}

	candidateSignatures := make([]exactAliasSignature, 0, repeats)
	controlSignatures := make([][]exactAliasSignature, len(controls))
	for round := 0; round < repeats; round++ {
		urls := append([]string{observation.CandidateURL}, observation.ControlURLs...)
		for index, probeURL := range urls {
			res, requestErr := fetchStatus(hc, st, method, probeURL)
			if requestErr != nil {
				return observation, requestErr
			}
			signature := exactAliasSignatureFromResponse(res)
			if index == 0 {
				candidateSignatures = append(candidateSignatures, signature)
			} else {
				controlSignatures[index-1] = append(controlSignatures[index-1], signature)
			}
		}
	}

	var candidateStable bool
	observation.Candidate, candidateStable = signaturesStable(candidateSignatures)
	controlOne, controlOneStable := signaturesStable(controlSignatures[0])
	controlTwo, controlTwoStable := signaturesStable(controlSignatures[1])
	observation.Control = controlOne
	if !candidateStable || !controlOneStable || !controlTwoStable {
		observation.Reason = "candidate or control changed across repetitions"
		return observation, nil
	}
	if controlOne != controlTwo {
		observation.Reason = "same-shape controls did not agree"
		return observation, nil
	}
	observation.Stable = true
	if observation.Candidate.transient() || observation.Control.transient() {
		observation.Reason = "transient, throttling, or server-error status was observed"
		return observation, nil
	}
	if observation.Candidate == observation.Control {
		observation.Reason = "candidate and controls have the same stable " + method + " signature"
		return observation, nil
	}
	observation.Differential = true
	observation.Reason = "stable candidate/control " + method + " differential"
	return observation, nil
}

func probeExactAlias(hc *http.Client, st *httpStats, base exactAliasBase, alias exactShortAlias) (exactAliasObservation, error) {
	repeats := args.ExactRepeats
	if repeats == 0 {
		repeats = 2
	}
	profile := args.ExactProfile
	if profile == "" {
		profile = "auto"
	}
	profiles := []string{profile}
	if profile == "auto" {
		if alias.Automatic {
			profiles = []string{"late-encoded", "late", "direct"}
		} else {
			profiles = []string{"direct"}
		}
	}
	method := strings.ToUpper(args.ExactMethod)
	methods := []string{method}
	if method == "AUTO" || method == "" {
		methods = []string{http.MethodHead, http.MethodOptions, http.MethodTrace}
	}

	var last exactAliasObservation
	var lastErr error
	successfulProfile := false
	for _, candidateProfile := range profiles {
		for _, candidateMethod := range methods {
			observation, err := probeExactAliasProfile(hc, st, base, alias, candidateProfile, candidateMethod, repeats)
			if err != nil {
				lastErr = err
				continue
			}
			successfulProfile = true
			last = observation
			if observation.Differential {
				return observation, nil
			}
		}
	}
	if !successfulProfile {
		return last, lastErr
	}
	if profile == "auto" {
		last.Profile = "auto"
		last.Reason = "no stable differential in the selected profile/method matrix"
	}
	return last, nil
}

func exactAliasEvidenceLabel(observation exactAliasObservation) string {
	if observation.Candidate.Status != observation.Control.Status {
		return fmt.Sprintf("%d/%d", observation.Candidate.Status, observation.Control.Status)
	}
	if observation.Candidate.ContentLength != observation.Control.ContentLength {
		return fmt.Sprintf("%d/%d length=%d/%d", observation.Candidate.Status, observation.Control.Status,
			observation.Candidate.ContentLength, observation.Control.ContentLength)
	}
	return fmt.Sprintf("%d/%d metadata", observation.Candidate.Status, observation.Control.Status)
}

func emitExactAliasObservation(base exactAliasBase, alias exactShortAlias, observation exactAliasObservation, probeErr error) {
	verified := observation.Differential
	lfnVerified := false
	var ordinalVerified *bool
	if alias.Automatic {
		ordinal := false
		ordinalVerified = &ordinal
	}
	oracle := observation.Reason
	if observation.Stable {
		oracle = strings.ToLower(observation.Method) + "-signature candidate={" + observation.Candidate.compact() +
			"} control={" + observation.Control.compact() + "} repeats=" + strconv.Itoa(observation.Repeats)
	}
	if probeErr != nil {
		oracle = "probe error: " + probeErr.Error()
	}
	result := resultOutput{
		Type: "alias-differential", FullMatch: observation.Differential, BaseUrl: base.URL,
		File: alias.filePart(), Tilde: alias.tildePart(), Ext: alias.extensionPart(),
		Partname: alias.name(), MatchType: observation.Profile,
		Status: observation.Candidate.Status, CollisionGroup: alias.collisionGroup(),
		OrdinalVerified: ordinalVerified, AliasVerified: &verified,
		LFNAssociationVerified: &lfnVerified, CustomSFNCandidate: alias.customSFNCandidate(),
		CanonicalGuardBypassCandidate: alias.guardBypassCandidate(),
		Oracle:                        oracle, Method: observation.Method,
	}
	if strings.HasPrefix(observation.Profile, "late") {
		result.ProbeSuffix = "split-before-tilde"
	}
	printJSON(result)

	if observation.Differential {
		classification := "automatic ~N alias"
		if alias.customSFNCandidate() {
			classification = "custom-SFN candidate"
		}
		line := fmt.Sprintf("[alias %s] %-18s exact-alias differential [%s/%s; %dx stable; %s; LFN association unverified]",
			exactAliasEvidenceLabel(observation), alias.name(), observation.Profile, observation.Method,
			observation.Repeats, classification)
		if args.FullUrl {
			line += " " + observation.CandidateURL
		}
		printHuman(color.HiGreenString(line))
		return
	}
	line := fmt.Sprintf("[alias no-diff] %-18s %s", alias.name(), oracle)
	printHuman(color.HiBlackString(line))
}

func runExactShortProbes(urls []string, hc *http.Client, st *httpStats) {
	aliases := make([]exactShortAlias, 0, len(args.ExactShorts))
	for _, rawAlias := range args.ExactShorts {
		alias, err := parseExactShortAlias(rawAlias)
		if err != nil {
			log.WithError(err).Error("Invalid exact short alias")
			continue
		}
		aliases = append(aliases, alias)
	}
	for _, rawBase := range urls {
		base, err := normalizeExactAliasBase(rawBase, args.ExactAppRoot)
		if err != nil {
			log.WithFields(log.Fields{"url": rawBase, "error": err}).Error("Unable to parse exact-short base URL")
			continue
		}
		printHuman("\n════════════════════════════════════════════════════════════════════════════════")
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("URL")+":", base.URL)
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("Mode") + ": exact 8.3 alias differential (HEAD/OPTIONS/TRACE auto; two same-shape controls)")
		printHuman("════════════════════════════════════════════════════════════════════════════════")
		for _, alias := range aliases {
			observation, probeErr := probeExactAlias(hc, st, base, alias)
			emitExactAliasObservation(base, alias, observation, probeErr)
		}
		printHuman("════════════════════════════════════════════════════════════════════════════════")
	}
	printFinishedStats(st)
}
