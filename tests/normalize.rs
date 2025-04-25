use uritemplate::UriTemplate;

// --- helper ---------------------------------------------------------------
fn template_str_after_normalize(tpl: &str) -> String {
    let mut t = UriTemplate::new(tpl).unwrap();
    t.normalize();
    t.to_string()
}

#[test]
fn normalize_sorts_and_dedupes_single_query() {
    let s = template_str_after_normalize("{?b,a,b,c,a}");
    assert_eq!(s, "{?a,b,c}");
}

#[test]
fn normalize_merges_multiple_query_segments() {
    let s = template_str_after_normalize("{?b,a}{&c}{&b}");
    assert_eq!(s, "{?a,b,c}");
}

#[test]
fn normalize_preserves_operator_when_first_is_ampersand() {
    let s = template_str_after_normalize("{&b,a,c}");
    assert_eq!(s, "{&a,b,c}");
}

#[test]
fn normalize_retains_varspec_details_of_first_occurrence() {
    // list* appears twice – only first (exploded) spec should be kept.
    let s = template_str_after_normalize("{?list*}{&list}{&a:3,b}");
    assert_eq!(s, "{?a:3,b,list*}");
}

#[test]
fn normalize_is_idempotent() {
    let mut t = UriTemplate::new("{?b,a,b}").unwrap();
    t.normalize();
    let once = t.to_string();
    t.normalize();
    let twice = t.to_string();
    assert_eq!(once, twice);
}

#[test]
fn normalize_does_not_affect_non_query_templates() {
    let original = "/foo{/bar}{#frag}";
    let s = template_str_after_normalize(original);
    assert_eq!(s, original);
}

#[test]
fn build_after_normalize_works() {
    let mut t = UriTemplate::new("/search{?q,b,a}").unwrap();
    t.normalize(); // becomes {?a,b,q}
    t.set("a", "1");
    t.set("q", "rust");
    assert_eq!(t.build(), "/search?a=1&q=rust");
}
