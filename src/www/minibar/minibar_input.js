
/* --- Input object --------------------------------------------------------- */

function Input(server,translations,opts) { // Input object constructor
    this.server=server;
    this.translations=translations;

    // Default values for options:
    this.options={
	delete_button_text: "⌫",
	default_source_language: null,
	startcat_menu: true,
	random_button: true,
	word_replacements: false
    }

    // Apply supplied options
    if(opts) for(var o in opts) this.options[o]=opts[o];

    // User interface elements
    this.main=empty("div");
    this.menus=empty("span");
    this.buttons=empty("span");
    this.surface=div_id("surface");
    this.words=div_id("words");
    this.from_menu=empty("select");
    this.startcat_menu=empty("select")

    with(this) {
	appendChildren(main,[surface,words]);
	if(options.startcat_menu)
	    appendChildren(menus,[text(" Startcat: "),startcat_menu])
	appendChildren(menus,[text(" From: "),from_menu])
	appendChildren(buttons,
		       [button(options.delete_button_text,bind(delete_last,this),"H"),
			button("Clear",bind(clear_all,this),"L")]);
	if(options.random_button)
	    buttons.appendChild(button("Random",bind(generate_random,this),"R"));
    }

    /* --- Input client state initialization --- */
    this.current={from: null, input: ""};
    this.previous=null;

    this.from_menu.onchange=bind(this.change_language,this);
    this.startcat_menu.onchange=bind(this.change_startcat,this);
}

Input.prototype.change_grammar=function (grammar) {
    var t=this;
    grammar.browse={} // for caching output from the browse command
    t.grammar=grammar;
    t.local=mi_local(t.server.current_grammar_url)
    update_language_menu(t.from_menu,grammar);
    set_initial_language(t.options,t.from_menu,grammar,t.local.get("from"));
    t.update_startcat_menu(grammar)
    t.change_language();
}

Input.prototype.update_startcat_menu=function (grammar) {
    var menu=this.startcat_menu;
    menu.innerHTML="";
    var cats=grammar.categories;
    for(var cat in cats) menu.appendChild(option(cats[cat],cats[cat]))
    var startcat=this.local.get("startcat") || grammar.startcat;
    if(startcat) menu.value=startcat;
    else {
	insertFirst(menu,option("Default",""));
	menu.value="";
    }
}

Input.prototype.change_startcat=function () {
    this.local.put("startcat",this.startcat_menu.value)
    this.clear_all();
}

Input.prototype.change_language=function () {
    this.current.from=this.from_menu.value;
    this.local.put("from",this.current.from)
    var old_current=this.local.get("current");
    var new_input= old_current && old_current.from==this.current.from
	           ? old_current.input : ""
    this.clear_all1();
    this.add_words(new_input)
}


Input.prototype.clear_all2=function() {
    with(this) {
	current.input="";
	local.put("current",current)
	previous=null;
	clear(surface)
	if(surface.typed) surface.appendChild(surface.typed)
    }
}


Input.prototype.clear_all1=function() {
    with(this) {
	remove_typed_input();
	clear_all2();
	translations.clear();
    }
}

Input.prototype.clear_all=function() {
    this.clear_all1();
    this.get_completions();
}

Input.prototype.get_completions=function() {
    with(this) {
	//debug("get_completions ");
	words.innerHTML="...";
	var args={from:current.from,input:current.input,cat:startcat_menu.value}
	server.complete(args,bind(show_completions,this));
	if(options.word_replacements) server.parse(args,bind(get_tree1,this));
    }
}

Input.prototype.show_completions=function(complete_output) {
    with(this) {
	//debug("show_completions ");
	var completions=complete_output[0].completions;
	var emptycnt=add_completions(completions)
	if(true/*emptycnt>0*/) translations.translateFrom(current,startcat_menu.value);
	else translations.clear();
	if(surface.typed && emptycnt==completions.length) {
	    if(surface.typed.value=="") remove_typed_input();
	}
	else add_typed_input();
    }
}

Input.prototype.add_completions=function(completions) {
    with(this) {
	if(words.timeout) clearTimeout(words.timeout),words.timeout=null;
	words.innerHTML="";
	words.completions=completions;
	words.word=[];
	var t=surface.typed ? surface.typed.value : "";
	var emptycnt=0;
	for(var i=0;i<completions.length;i++) {
	    var s=completions[i];
	    if(s.length>0) {
		var w=word(s);
		words.appendChild(w);
		words.word[i]=w;
	    }
	    else emptycnt++;
	}
	filter_completions(t,true);
	return emptycnt;
    }
}

Input.prototype.filter_completions=function(t,dim) {
    with(this) {
	if(words.timeout) clearTimeout(words.timeout),words.timeout=null;
	words.filtered=t;
	//if(dim) debug('filter "'+t+'"');
	var w=words.word;
	words.count=0;
	var dimmed=0;
	var prefix=""; // longest common prefix, for completion
	for(var i=0;i<w.length;i++) {
	    var s=words.completions[i];
	    var keep=hasPrefix(s,t);
	    if(keep) {
		if(words.count==0) prefix=s;
		else prefix=(commonPrefix(prefix,s));
		words.count++;
	    }
	    if(dim) {
		w[i].style.opacity= keep ? "1" : "0.5";
		if(keep) w[i].style.display="inline";
		else dimmed++;
	    }
	    else 
		w[i].style.display=keep ? "inline" : "none";
	}
	words.theword=prefix;
	if(dimmed>0)
	    words.timeout=setTimeout(function(){ filter_completions(t,false)},1000);
    }
}


Input.prototype.add_typed_input=function() {
    with(this) {
	if(!surface.typed) {
	    var inp=empty("input","type","text");
	    inp.value="";
	    inp.setAttribute("accesskey","t");
	    inp.style.width="10em";
	    inp.onkeyup=bind(complete_typed,this);
	    surface.appendChild(inp);
	    surface.typed=inp;
	    inp.focus();
	}
    }
}

Input.prototype.remove_typed_input=function() {
    with(this) {
	if(surface.typed) {
	    surface.typed.parentNode.removeChild(surface.typed);
	    surface.typed=null;
	}
    }
}

Input.prototype.complete_typed=function(event) {
    with(this) {
	//element("debug").innerHTML=show_props(event,"event");
	var inp=surface.typed;
	//debug('"'+inp.value+'"');
	var s=inp.value;
	var ws=s.split(" ");
	if(ws.length>1 || event.keyCode==13) {
	    if(ws[0]!=words.filtered) filter_completions(ws[0],true);
	    if(words.count==1) add_word(words.theword);
	    else if(event.keyCode==13) add_word(ws[0]) // for literals
	    else if(elem(ws[0],words.completions)) add_word(ws[0]);
	    else if(words.theword.length>ws[0].length) inp.value=words.theword;
	}
	else if(s!=words.filtered) filter_completions(s,true)
    }
}

Input.prototype.generate_random=function() {
    var t=this;
    function show_random(random) {
	t.clear_all1();
	t.add_words(random[0].text);
    }
    
    function lin_random(abs) {
	t.server.linearize({tree:abs[0].tree,to:t.current.from},show_random);
    }
    t.server.get_random({cat:t.startcat_menu.value},lin_random);
}

Input.prototype.add_words=function(s) {
    this.add_words1(s);
    this.get_completions();
}

Input.prototype.add_words1=function(s) {
    var ws=s.split(" ");
    for(var i=0;i<ws.length;i++)
	if(ws[i]) this.add_word1(ws[i]+" ");
}

Input.prototype.word=function(s) { 
    var t=this;
    function click_word() {
	if(t.surface.typed) t.surface.typed.value="";
	t.add_word(s);
    }
    return button(s,click_word);
}

Input.prototype.add_word=function(s) {
    with(this) {
	add_word1(s+" ");
	if(surface.typed) {
	    var s2;
	    if(hasPrefix(s2=surface.typed.value,s)) {
		s2=s2.substr(s.length);
		while(s2.length>0 && s2[0]==" ") s2=s2.substr(1);
		surface.typed.value=s2;
	    }
	    else surface.typed.value="";
	}
	get_completions();
    }
}

Input.prototype.add_word1=function(s) {
    with(this) {
	previous={ input: current.input, previous: previous };
	current.input+=s;
	local.put("current",current)
	var w=span_class("word",text(s));
	if(surface.typed) surface.insertBefore(w,surface.typed);
	else surface.appendChild(w);
    }
}

Input.prototype.delete_last=function() {
    with(this) {
	if(surface.typed && surface.typed.value!="")
	    surface.typed.value="";
	else if(previous) {
	    current.input=previous.input;
	    local.put("current",current)
	    previous=previous.previous;
	    if(surface.typed) {
		surface.removeChild(surface.typed.previousSibling);
		surface.typed.focus();
	    }
	    else surface.removeChild(surface.lastChild);
	    translations.clear();
	    get_completions();
	}
    }
}

/* --- Structural editing --------------------------------------------------- */

Input.prototype.get_tree1=function(parse) {
    var t=this;
    function proceed(lin) { t.get_tree2(lin,parse[0].trees[0]) }

    if(parse.length==1 && parse[0].from==t.current.from
       && parse[0].trees && parse[0].trees.length==1)
	t.server.linearize({to:t.current.from,tree:parse[0].trees[0]},proceed);
    else t.end_structural_editing();
}

Input.prototype.get_tree2=function(lin,tree) {
    var t=this;
    with(t) {
	if(lin.length==1 && lin[0].to==current.from
	   && lin[0].text+" "==current.input
	   && (lin[0].brackets)) {
	    var bs=lin[0].brackets;
	    //var tree=show_abstract_tree(bs);
	    function proceed() { t.enable_structural_editing(bs,tree) }
	    server.linearize({to:current.from,tree:tree},
			     proceed,bind(end_structural_editing,t))
	}
	else end_structural_editing();
    }
}

Input.prototype.end_structural_editing=function() {
    var t=this;
    if(t.surface.structural_editing_enabled) {
	var s=t.current.input;
	t.clear_all2()
	t.add_words1(s);
	t.surface.structural_editing_enabled=false;
    }
}

Input.prototype.enable_structural_editing=function(brackets,tree) {
    var t=this;
    with(t) {
	function add_bs(b,parent) {
	    if(b.token) {
		var fun=parent.fun,cat=parent.cat;
		function showrepl() { t.show_replacements(brackets,parent,tree)}
		var w= span_class("word editable",text(b.token));
		if(fun && cat) w.onclick=showrepl
		w.title=(fun||"_")+":"+(cat||"_")+" "+parent.fid+":"+parent.index
		surface.appendChild(w);
	    }
	    else b.children.map(function(c){add_bs(c,b)})
	}
	var typed=surface.typed;
	clear(surface)
	add_bs(brackets);
	t.surface.structural_editing_enabled=true;
	if(typed) surface.appendChild(typed);
    }
}

Input.prototype.show_replacements=function(brackets,parent,tree) {
    var fun=parent.fun,cat=parent.cat;
    var t=this;
    with(t) {
	function browse1(fun_info) {
	    var fun_type = fun_info.def.split(":")[1];
	    function browse2(cat_info) {
		var extb=null;
		function examine_replacement(rfun) {
		    function browse3(rfun_info) {
			var rfun_type=rfun_info.def.split(":")[1];
			function replace() {
			    t.replace_word(brackets,parent,rfun,tree);
			}
			if(rfun_type==fun_type)
			    t.words.insertBefore(button(rfun,replace),extb);
		    }
		    t.browse(rfun,browse3)
		}
		var ps=cat_info.producers;
		clear(t.words);
		if(t.options.extend_grammar) {
		    extb=button("New "+cat+"...",
				function() { t.options.extend_grammar(cat,fun_type)})
		    t.words.appendChild(extb)
		}
		if(ps)
		    for(var pi in ps)
			if(ps[pi]!=fun) examine_replacement(ps[pi])
	    }
	    t.browse(cat,browse2)
	}
	t.browse(fun,browse1)
    }
}

Input.prototype.replace_word=function(brackets,parent,fun,tree) {
    var t=this;
    function proceed(tree) {
	//parent.fun=fun;
	//var tree=show_abstract_tree(brackets);
	tree=modify_tree(tree,parent.fid,fun)
	tree=show_tree(tree) // Convert JSON repr of tree back to string
	function replace(lin_output) {
	    if(lin_output.length==1 && lin_output[0].to==t.current.from) {
		t.clear_all1();
		t.add_words(lin_output[0].text)
	    }
	}
	function err(text,status,ctype) {
	    t.words.innerHTML=
		ctype.split(";")[0]=="text/html"
		? text
		: "Word replacement failed"
	}
	t.server.linearize({to:t.current.from,tree:tree},replace,err)
    }
    // Convert the string representaiton of the abstract syntax tree to JSON:
    t.server.pgf_call("abstrjson",{tree:tree},proceed)
}

Input.prototype.browse=function(id,cont) {
    var t=this;
    if(t.grammar.browse[id]) cont(t.grammar.browse[id])
    else {
	function browsed(info) {
	    t.grammar.browse[id]=info;
	    cont(info);
	}
	t.server.browse(id,browsed);
    }
}


/* --- Auxiliary functions -------------------------------------------------- */


function mi_local(grammar_url) {
    function dummy() {
	return {
	    get: function(name,def) { return def },
	    put: function(name,value) { }
	}
    }
    function real() {
	var prefix="gf.minibar_input."+grammar_url+"."
	return {
	    get: function (name,def) {
		var id=prefix+name
		return localStorage[id] ? JSON.parse(localStorage[id]) : def;
	    },
	    put: function (name,value) {
		var id=prefix+name;
		localStorage[id]=JSON.stringify(value);
	    }
	}
    }
    return window.localStorage ? real() : dummy()
}


function set_initial_language(options,menu,grammar,old_from) {
    var user_from=old_from || grammar.userLanguage;
    if(user_from) menu.value=user_from; // !! What if the language was removed?
    else if(options.default_source_language) {
	for(var i=0;i<menu.options.length;i++) {
	    var o=menu.options[i].value;
	    var l=langpart(o,grammar.name);
	    if(l==options.default_source_language) menu.value=o;
	}
    }
}

/*
function show_abstract_tree(b) { return show_tree(abstract_tree(b)) }

function abstract_tree(b) {
    return { fun:b.fun,children:abstract_trees(b.children) }
}

function abstract_trees(bs) {
    var as=[];
    for(var i in bs)
	if(bs[i].fun) as.push(abstract_tree(bs[i]))
    return as
}
*/

function show_tree(t) {
    return t.children
	? t.fun+" "+t.children.map(show_tree_atomic).join(" ")
	: t.fun;
}

function show_tree_atomic(t) {
    var s=show_tree(t);
    return t.children && t.children.length>0 ? "("+s+")" : s
}

// Find the node labelled fid in tree and replace the function there with fun
function modify_tree(tree,fid,fun) {
    if(tree.fun) {
	if(tree.fid==fid) tree.fun=fun
	else if(tree.children)
	    tree.children.map(function(t) { modify_tree(t,fid,fun) })
    }
    return tree;
}
