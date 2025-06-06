// File autogenerated with /scripts/generate_tests.py

use uritemplate::UriTemplate;

// Additional Examples 1
#[test]
fn test_additional_examples_1() {
    let mut templates = [
        UriTemplate::new("{/id*}").unwrap(),
        UriTemplate::new("{/id*}{?fields,first_name,last.name,token}").unwrap(),
        UriTemplate::new("/search.{format}{?q,geocode,lang,locale,page,result_type}").unwrap(),
        UriTemplate::new("/test{/Some%20Thing}").unwrap(),
        UriTemplate::new("/set{?number}").unwrap(),
        UriTemplate::new("/loc{?long,lat}").unwrap(),
        UriTemplate::new("/base{/group_id,first_name}/pages{/page,lang}{?format,q}").unwrap(),
        UriTemplate::new("/sparql{?query}").unwrap(),
        UriTemplate::new("/go{?uri}").unwrap(),
        UriTemplate::new("/service{?word}").unwrap(),
        UriTemplate::new("/lookup{?Stra%C3%9Fe}").unwrap(),
        UriTemplate::new("{random}").unwrap(),
        UriTemplate::new("{?assoc_special_chars*}").unwrap(),
    ];

    for i in 0..templates.len() {
        templates[i].set("id", "person");
        templates[i].set("token", "12345");
        templates[i].set("fields", &["id", "name", "picture"] as &[&str]);
        templates[i].set("format", "json");
        templates[i].set("q", "URI Templates");
        templates[i].set("page", "5");
        templates[i].set("lang", "en");
        templates[i].set("geocode", &["37.76", "-122.427"] as &[&str]);
        templates[i].set("first_name", "John");
        templates[i].set("last.name", "Doe");
        templates[i].set("Some%20Thing", "foo");
        templates[i].set("number", "6");
        templates[i].set("long", "37.76");
        templates[i].set("lat", "-122.427");
        templates[i].set("group_id", "12345");
        templates[i].set("query", "PREFIX dc: <http://purl.org/dc/elements/1.1/> SELECT ?book ?who WHERE { ?book dc:creator ?who }");
        templates[i].set("uri", "http://example.org/?uri=http%3A%2F%2Fexample.org%2F");
        templates[i].set("word", "drücken");
        templates[i].set("Stra%C3%9Fe", "Grüner Weg");
        templates[i].set("random", "šöäŸœñê€£¥‡ÑÒÓÔÕÖ×ØÙÚàáâãäåæçÿ");
        templates[i].set(
            "assoc_special_chars",
            &[("šöäŸœñê€£¥‡ÑÒÓÔÕ", "Ö×ØÙÚàáâãäåæçÿ")] as &[(&str, &str)],
        );
    }

    assert_eq!(templates[0].build(), "/person");
    let template_1_answers = vec![
        "/person?fields=id,name,picture&first_name=John&last.name=Doe&token=12345",
        "/person?fields=id,picture,name&first_name=John&last.name=Doe&token=12345",
        "/person?fields=picture,name,id&first_name=John&last.name=Doe&token=12345",
        "/person?fields=picture,id,name&first_name=John&last.name=Doe&token=12345",
        "/person?fields=name,picture,id&first_name=John&last.name=Doe&token=12345",
        "/person?fields=name,id,picture&first_name=John&last.name=Doe&token=12345",
    ];
    assert!(template_1_answers.contains(&templates[1].build().as_str()));
    let template_2_answers = vec![
        "/search.json?q=URI%20Templates&geocode=37.76,-122.427&lang=en&page=5",
        "/search.json?q=URI%20Templates&geocode=-122.427,37.76&lang=en&page=5",
    ];
    assert!(template_2_answers.contains(&templates[2].build().as_str()));
    assert_eq!(templates[3].build(), "/test/foo");
    assert_eq!(templates[4].build(), "/set?number=6");
    assert_eq!(templates[5].build(), "/loc?long=37.76&lat=-122.427");
    assert_eq!(
        templates[6].build(),
        "/base/12345/John/pages/5/en?format=json&q=URI%20Templates"
    );
    assert_eq!(templates[7].build(), "/sparql?query=PREFIX%20dc%3A%20%3Chttp%3A%2F%2Fpurl.org%2Fdc%2Felements%2F1.1%2F%3E%20SELECT%20%3Fbook%20%3Fwho%20WHERE%20%7B%20%3Fbook%20dc%3Acreator%20%3Fwho%20%7D");
    assert_eq!(
        templates[8].build(),
        "/go?uri=http%3A%2F%2Fexample.org%2F%3Furi%3Dhttp%253A%252F%252Fexample.org%252F"
    );
    assert_eq!(templates[9].build(), "/service?word=dr%C3%BCcken");
    assert_eq!(
        templates[10].build(),
        "/lookup?Stra%C3%9Fe=Gr%C3%BCner%20Weg"
    );
    assert_eq!(templates[11].build(), "%C5%A1%C3%B6%C3%A4%C5%B8%C5%93%C3%B1%C3%AA%E2%82%AC%C2%A3%C2%A5%E2%80%A1%C3%91%C3%92%C3%93%C3%94%C3%95%C3%96%C3%97%C3%98%C3%99%C3%9A%C3%A0%C3%A1%C3%A2%C3%A3%C3%A4%C3%A5%C3%A6%C3%A7%C3%BF");
    assert_eq!(templates[12].build(), "?%C5%A1%C3%B6%C3%A4%C5%B8%C5%93%C3%B1%C3%AA%E2%82%AC%C2%A3%C2%A5%E2%80%A1%C3%91%C3%92%C3%93%C3%94%C3%95=%C3%96%C3%97%C3%98%C3%99%C3%9A%C3%A0%C3%A1%C3%A2%C3%A3%C3%A4%C3%A5%C3%A6%C3%A7%C3%BF");
}

// Additional Examples 2
#[test]
fn test_additional_examples_2() {
    let mut templates = [
        UriTemplate::new("{/id*}").unwrap(),
        UriTemplate::new("{/id*}{?fields,token}").unwrap(),
    ];

    for i in 0..templates.len() {
        templates[i].set("id", &["person", "albums"] as &[&str]);
        templates[i].set("token", "12345");
        templates[i].set("fields", &["id", "name", "picture"] as &[&str]);
        templates[i].set("format", "atom");
        templates[i].set("q", "URI Templates");
        templates[i].set("page", "10");
        templates[i].set("start", "5");
        templates[i].set("lang", "en");
        templates[i].set("geocode", &["37.76", "-122.427"] as &[&str]);
    }

    let template_0_answers = vec!["/person/albums", "/albums/person"];
    assert!(template_0_answers.contains(&templates[0].build().as_str()));
    let template_1_answers = vec![
        "/person/albums?fields=id,name,picture&token=12345",
        "/person/albums?fields=id,picture,name&token=12345",
        "/person/albums?fields=picture,name,id&token=12345",
        "/person/albums?fields=picture,id,name&token=12345",
        "/person/albums?fields=name,picture,id&token=12345",
        "/person/albums?fields=name,id,picture&token=12345",
        "/albums/person?fields=id,name,picture&token=12345",
        "/albums/person?fields=id,picture,name&token=12345",
        "/albums/person?fields=picture,name,id&token=12345",
        "/albums/person?fields=picture,id,name&token=12345",
        "/albums/person?fields=name,picture,id&token=12345",
        "/albums/person?fields=name,id,picture&token=12345",
    ];
    assert!(template_1_answers.contains(&templates[1].build().as_str()));
}

// Additional Examples 3: Empty Variables
#[test]
fn test_additional_examples_3() {
    let mut templates = [
        UriTemplate::new("{/empty_list}").unwrap(),
        UriTemplate::new("{/empty_list*}").unwrap(),
        UriTemplate::new("{?empty_list}").unwrap(),
        UriTemplate::new("{?empty_list*}").unwrap(),
        UriTemplate::new("{?empty_assoc}").unwrap(),
        UriTemplate::new("{?empty_assoc*}").unwrap(),
    ];

    for i in 0..templates.len() {
        templates[i].set("empty_list", &[] as &[&str]);
        templates[i].set("empty_assoc", &[] as &[(&str, &str)]);
    }

    let template_0_answers = vec![""];
    assert!(template_0_answers.contains(&templates[0].build().as_str()));
    let template_1_answers = vec![""];
    assert!(template_1_answers.contains(&templates[1].build().as_str()));
    let template_2_answers = vec![""];
    assert!(template_2_answers.contains(&templates[2].build().as_str()));
    let template_3_answers = vec![""];
    assert!(template_3_answers.contains(&templates[3].build().as_str()));
    let template_4_answers = vec![""];
    assert!(template_4_answers.contains(&templates[4].build().as_str()));
    let template_5_answers = vec![""];
    assert!(template_5_answers.contains(&templates[5].build().as_str()));
}

// Additional Examples 4: Numeric Keys
#[test]
fn test_additional_examples_4() {
    let mut templates = [
        UriTemplate::new("{42}").unwrap(),
        UriTemplate::new("{?42}").unwrap(),
        UriTemplate::new("{1337}").unwrap(),
        UriTemplate::new("{?1337*}").unwrap(),
        UriTemplate::new("{?german*}").unwrap(),
    ];

    for i in 0..templates.len() {
        templates[i].set(
            "42",
            "The Answer to the Ultimate Question of Life, the Universe, and Everything",
        );
        templates[i].set("1337", &["leet", "as", "it", "can", "be"] as &[&str]);
        templates[i].set(
            "german",
            &[("11", "elf"), ("12", "zwölf")] as &[(&str, &str)],
        );
    }

    assert_eq!(templates[0].build(), "The%20Answer%20to%20the%20Ultimate%20Question%20of%20Life%2C%20the%20Universe%2C%20and%20Everything");
    assert_eq!(templates[1].build(), "?42=The%20Answer%20to%20the%20Ultimate%20Question%20of%20Life%2C%20the%20Universe%2C%20and%20Everything");
    assert_eq!(templates[2].build(), "leet,as,it,can,be");
    assert_eq!(
        templates[3].build(),
        "?1337=leet&1337=as&1337=it&1337=can&1337=be"
    );
    let template_4_answers = vec!["?11=elf&12=zw%C3%B6lf", "?12=zw%C3%B6lf&11=elf"];
    assert!(template_4_answers.contains(&templates[4].build().as_str()));
}
