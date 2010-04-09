// minibar.js, assumes that support.js has also been loaded

/* --- Configuration -------------------------------------------------------- */

var server="http://www.grammaticalframework.org:41296"
//var server="http://tournesol.cs.chalmers.se:41296";
//var server="http://localhost:41296";
var grammars_url=server+"/grammars/";

var tree_icon=server+"/translate/se.chalmers.cs.gf.gwt.TranslateApp/tree-btn.png";

/* --- Grammar access object ------------------------------------------------ */

var server = {
    // State variables (private):
    current_grammar_url: grammars_url+"Foods.pgf",
    // Methods:
    switch_grammar: function(grammar_name) {
	this.current_grammar_url=grammars_url+grammar_name;
    },
    
    get_grammarlist: function() {
	jsonp(grammars_url+"grammars.cgi") // calls show_grammarlist
    },
    get_languages: function(cont_name) {
	jsonp(this.current_grammar_url,cont_name);
    },
    get_random: function(cont_name) {
	jsonp(this.current_grammar_url+"?command=random&random="+Math.random(),cont_name);
    },
    linearize: function(tree,to,cont_name) {
	jsonp(this.current_grammar_url+"?command=linearize&tree="
	      +encodeURIComponent(tree)+"&to="+to,cont_name)
    },
    complete: function(from,input,cont_name) {
	jsonp(this.current_grammar_url
	      +"?command=complete"
	      +"&from="+encodeURIComponent(from)
	      +"&input="+encodeURIComponent(input),
	      cont_name);

    },
    translate: function(from,input,cont_name) {
	jsonp(this.current_grammar_url
	      +"?command=translate"
	      +"&from="+encodeURIComponent(from)
	      +"&input="+encodeURIComponent(input),
	      cont_name)
    }

};

/* --- Initialisation ------------------------------------------------------- */

function start_minibar() { // typically called when the HTML document is loaded
  var minibar=element("minibar");
  minibar.appendChild(div_id("menubar"));
  minibar.appendChild(div_id("surface"));
  minibar.appendChild(div_id("words"));
  minibar.appendChild(div_id("translations"));
  server.get_grammarlist(); // calls show_grammarlist
}


/* --- Functions ------------------------------------------------------------ */

function show_grammarlist(grammars) {
  var menu=empty("select");
  for(var i=0;i<grammars.length;i++) {
    var opt=empty("option");
    opt.setAttribute("value",grammars[i]);
    opt.innerHTML=grammars[i];
    menu.appendChild(opt);
  }
  menu.setAttribute("onchange","new_grammar(this)");
  var menubar=element("menubar");
  menubar.innerHTML="Grammar: ";
  menubar.appendChild(menu);
  menubar.appendChild(text(" Input language: "));
  menubar.appendChild(empty_id("select","language_menu"));
  menubar.appendChild(button("Clear","clear_all()"));
  menubar.appendChild(button("⌫","delete_last()"));
  menubar.appendChild(button("Random","generate_random()"));
  select_grammar(grammars[0]);
}

function new_grammar(menu) {
  select_grammar(menu.options[menu.selectedIndex].value);
}

function select_grammar(grammar_name) {
    server.switch_grammar(grammar_name);
    server.get_languages("show_languages");
}

function show_languages(grammar) {
  var r="";
  var lang=grammar.languages;
  var menu=element("language_menu");
  menu.setAttribute("onchange","new_language(this)");
  menu.grammar=grammar;
  menu.innerHTML="";
  for(var i=0; i<lang.length; i++) {
    if(lang[i].canParse) {
      var opt=empty("option");
      opt.setAttribute("value",""+i);
      opt.innerHTML=lang[i].name;
      menu.appendChild(opt);
    }
  }
  new_language(menu);
}

function new_language(menu) {
  var ix=menu.options[menu.selectedIndex].value;
  var langname=menu.grammar.languages[ix].name;
  menu.current={from: langname, input: ""};
  clear_all();
}

function clear_all1() {
  var menu=element("language_menu");
  menu.current.input="";
  menu.previous=null;
  element("surface").innerHTML="";
  element("translations").innerHTML="";
  return menu;
}

function clear_all() {
  get_completions(clear_all1());
}

function delete_last() {
  var menu=element("language_menu");
  if(menu.previous) {
    menu.current.input=menu.previous.input;
    menu.previous=menu.previous.previous;
    var s=element("surface");
    s.removeChild(s.lastChild);
    element("translations").innerHTML="";
    get_completions(menu);
  }
}

function generate_random() {
    server.get_random("lin_random");
//  jsonp(server.current_grammar_url+"?command=random&random="+Math.random(),"lin_random");
}

function lin_random(abs) {
  var menu=element("language_menu");
  var lang=menu.current.from;
  server.linearize(abs[0].tree,lang,"show_random");
/*
  jsonp(server.current_grammar_url+"?command=linearize&tree="+encodeURIComponent(abs[0].tree)
	+"&to="+lang,
	"show_random")
*/	
}

function show_random(random) {
  var menu=clear_all1();
  var words=random[0].text.split(" ");
  for(var i=0;i<words.length;i++)
    add_word1(menu,words[i]+" ");
  element("words").innerHTML="...";
  get_completions(menu);
}

function get_completions(menu) {
  var c=menu.current;
  server.complete(c.from,c.input,"show_completions");
/*
  jsonp(server.current_grammar_url
	+"?command=complete"
	+"&from="+encodeURIComponent(c.from)
	+"&input="+encodeURIComponent(c.input),
	"show_completions");
*/
}

function word(s) {
  var w=div_class("word",text(s));
  w.setAttribute("onclick",'add_word("'+s+'")');
  return w;
}

function add_word1(menu,s) {
  menu.previous={ input: menu.current.input, previous: menu.previous };
  menu.current.input+=s;
  element("surface").appendChild(span_class("word",text(s)));
}

function add_word(s) {
  var menu=element("language_menu");
  add_word1(menu,s);
  element("words").innerHTML="...";
  get_completions(menu);
}

function show_completions(completions) {
  var box=element("words");
  var menu=element("language_menu");
  var prefixlen=menu.current.input.length;
  var emptycnt=0;
  box.innerHTML="";
  for(var i=0;i<completions.length;i++) {
    var s=completions[i].text.substring(prefixlen);
    if(s.length>0) box.appendChild(word(s));
    else emptycnt++;
  }
  if(emptycnt>0)
    //setTimeout(function(){get_translations(menu);},200);
    get_translations(menu);
}

function get_translations(menu) {
  server.translate(menu.current.from,menu.current.input,"show_translations");
/*
  jsonp(server.current_grammar_url
	+"?command=translate"
	+"&from="+encodeURIComponent(menu.current.from)
	+"&input="+encodeURIComponent(menu.current.input),
	"show_translations")
*/
}

function show_translations(translations) {
  var trans=element("translations");
  var cnt=translations.length;
  trans.innerHTML="";
  trans.appendChild(wrap("h3",text(cnt<1 ? "No translations?" :
				   cnt>1 ? ""+cnt+" translations:":
				   "One translation:")));
  for(p=0;p<cnt;p++) {
    var t=translations[p];
    var lin=t.linearizations;
    var tbody=empty("tbody");
    if(t.tree)
      tbody.appendChild(tr([th(text("Abstract: ")),
			    tda([abstree_button(t.tree),text(" "+t.tree)])]));
    for(var i=0;i<lin.length;i++)
      tbody.appendChild(tr([th(text(lin[i].to+": ")),
			    tda([parsetree_button(t.tree,lin[i].to),text(lin[i].text)])]));
    trans.appendChild(wrap("table",tbody));
  }
}

function abstree_button(abs) {
  var i=img(tree_icon);
  i.setAttribute("onclick","toggle_img(this)");
  i.other=server.current_grammar_url+"?command=abstrtree&tree="+encodeURIComponent(abs);
  return i;
}

function parsetree_button(abs,lang) {
  var i=img(tree_icon);
  i.setAttribute("onclick","toggle_img(this)");
  i.other=server.current_grammar_url
          +"?command=parsetree&from="+lang+"&tree="+encodeURIComponent(abs);
  return i;
}

function toggle_img(i) {
  var tmp=i.src;
  i.src=i.other;
  i.other=tmp;
}


/*
se.chalmers.cs.gf.gwt.TranslateApp/align-btn.png

GET /grammars/Foods.pgf?&command=abstrtree&tree=Pred+(This+Fish)+(Very+Fresh)
GET /grammars/Foods.pgf?&command=parsetree&tree=Pred+(This+Fish)+Expensive&from=FoodsAfr
GET /grammars/Foods.pgf?&command=alignment&tree=Pred+(This+Fish)+Expensive
*/
