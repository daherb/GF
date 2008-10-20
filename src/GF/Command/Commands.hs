module GF.Command.Commands (
  allCommands,
  lookCommand,
  exec,
  isOpt,
  options,
  flags,
  CommandInfo,
  CommandOutput
  ) where

import PGF
import PGF.CId
import PGF.ShowLinearize
import PGF.Macros
import PGF.Data ----
import PGF.Morphology
import PGF.VisualizeTree
import GF.Compile.Export
import GF.Infra.Option (noOptions)
import GF.Infra.UseIO
import GF.Data.ErrM ----
import PGF.Expr (readTree)
import GF.Command.Abstract
import GF.Command.Messages
import GF.Text.Lexing
import GF.Text.Transliterations
import GF.Quiz

import GF.Command.TreeOperations ---- temporary place for typecheck and compute

import GF.Data.Operations
import GF.Text.Coding

import Data.Maybe
import qualified Data.Map as Map
import System.Cmd

import Debug.Trace

type CommandOutput = ([Tree],String) ---- errors, etc

data CommandInfo = CommandInfo {
  exec     :: [Option] -> [Tree] -> IO CommandOutput,
  synopsis :: String,
  syntax   :: String,
  explanation :: String,
  longname :: String,
  options  :: [(String,String)],
  flags    :: [(String,String)],
  examples :: [String]
  }

emptyCommandInfo :: CommandInfo
emptyCommandInfo = CommandInfo {
  exec = \_ ts -> return (ts,[]), ----
  synopsis = "",
  syntax = "",
  explanation = "",
  longname = "",
  options = [],
  flags = [],
  examples = []
  }

lookCommand :: String -> Map.Map String CommandInfo -> Maybe CommandInfo
lookCommand = Map.lookup

commandHelpAll :: String -> PGF -> [Option] -> String
commandHelpAll cod pgf opts = unlines
  [commandHelp (isOpt "full" opts) (co,info)
    | (co,info) <- Map.assocs (allCommands cod pgf)]

commandHelp :: Bool -> (String,CommandInfo) -> String
commandHelp full (co,info) = unlines $ [
  co ++ ", " ++ longname info,
  synopsis info] ++ if full then [
  "",
  "syntax:" ++++ "  " ++ syntax info,
  "",
  explanation info,
  "options:" ++++ unlines [" -" ++ o ++ "\t" ++ e | (o,e) <- options info],
  "flags:" ++++ unlines [" -" ++ o ++ "\t" ++ e | (o,e) <- flags info],
  "examples:" ++++ unlines ["  " ++ s | s <- examples info]
  ] else []

-- this list must no more be kept sorted by the command name
allCommands :: String -> PGF -> Map.Map String CommandInfo
allCommands cod pgf = Map.fromList [
  ("cc", emptyCommandInfo {
     longname = "compute_concrete",
     syntax = "cc (-all | -table | -unqual)? TERM",
     synopsis = "computes concrete syntax term using a source grammar",
     explanation = unlines [
       "Compute TERM by concrete syntax definitions. Uses the topmost",
       "module (the last one imported) to resolve constant names.",
       "N.B.1 You need the flag -retain when importing the grammar, if you want",
       "the definitions to be retained after compilation.",
       "N.B.2 The resulting term is not a tree in the sense of abstract syntax",
       "and hence not a valid input to a Tree-expecting command.",
       "This command must be a line of its own, and thus cannot be a part",
       "of a pipe."
       ],
     options = [
       ("all","pick all strings (forms and variants) from records and tables"),
       ("table","show all strings labelled by parameters"),
       ("unqual","hide qualifying module names")
       ]
     }),
  ("dc",  emptyCommandInfo {
     longname = "define_command",
     syntax = "dc IDENT COMMANDLINE",
     synopsis = "define a command macro",
     explanation = unlines [
       "Defines IDENT as macro for COMMANDLINE, until IDENT gets redefined.",
       "A call of the command has the form %IDENT. The command may take an", 
       "argument, which in COMMANDLINE is marked as ?0. Both strings and",
       "trees can be arguments. Currently at most one argument is possible.",
       "This command must be a line of its own, and thus cannot be a part",
       "of a pipe."
       ] 
     }),
  ("dt",  emptyCommandInfo {
     longname = "define_tree",
     syntax = "dt IDENT (TREE | STRING | \"<\" COMMANDLINE)",
     synopsis = "define a tree or string macro",
     explanation = unlines [
       "Defines IDENT as macro for TREE or STRING, until IDENT gets redefined.",
       "The defining value can also come from a command, preceded by \"<\".",
       "If the command gives many values, the first one is selected.",
       "A use of the macro has the form %IDENT. Currently this use cannot be",
       "a subtree of another tree. This command must be a line of its own",
       "and thus cannot be a part of a pipe."
       ],
     examples = [
       ("dt ex \"hello world\"                    -- define ex as string"),
       ("dt ex UseN man_N                         -- define ex as string"),
       ("dt ex < p -cat=NP \"the man in the car\" -- define ex as parse result"),
       ("l -lang=LangSwe %ex | ps -to_utf8        -- linearize the tree ex")
       ] 
     }),
  ("e",  emptyCommandInfo {
     longname = "empty",
     synopsis = "empty the environment"
     }),
  ("gr", emptyCommandInfo {
     longname = "generate_random",
     synopsis = "generate random trees in the current abstract syntax",
     syntax = "gr [-cat=CAT] [-number=INT]",
     examples = [
       "gr                     -- one tree in the startcat of the current grammar",
       "gr -cat=NP -number=16  -- 16 trees in the category NP",
       "gr -lang=LangHin,LangTha -cat=Cl  -- Cl, both in LangHin and LangTha"
       ],
     explanation = unlines [
       "Generates a list of random trees, by default one tree."
----       "If a tree argument is given, the command completes the Tree with values to",
----       "the metavariables in the tree."
       ],
     flags = [
       ("cat","generation category"),
       ("lang","uses only functions that have linearizations in all these languages"),
       ("number","number of trees generated")
       ],
     exec = \opts _ -> do
       let pgfr = optRestricted opts
       ts <- generateRandom pgfr (optType opts)
       return $ fromTrees $ take (optNum opts) ts
     }),
  ("gt", emptyCommandInfo {
     longname = "generate_trees",
     synopsis = "generates a list of trees, by default exhaustive",
     explanation = unlines [
       "Generates all trees of a given category, with increasing depth.",
       "By default, the depth is 4, but this can be changed by a flag."
       ---- "If a Tree argument is given, the command completes the Tree with values",
       ---- "to the metavariables in the tree."
       ],
     flags = [
       ("cat","the generation category"),
       ("depth","the maximum generation depth"),
       ("lang","excludes functions that have no linearization in this language"),
       ("number","the number of trees generated")
       ],
     exec = \opts _ -> do
       let pgfr = optRestricted opts
       let dp = return $ valIntOpts "depth" 4 opts
       let ts = generateAllDepth pgfr (optType opts) dp
       return $ fromTrees $ take (optNumInf opts) ts
     }),
  ("h", emptyCommandInfo {
     longname = "help",
     syntax = "h (-full)? COMMAND?",
     synopsis = "get description of a command, or a the full list of commands",
     explanation = unlines [
       "Displays information concerning the COMMAND.",
       "Without argument, shows the synopsis of all commands."
       ],
     options = [
       ("changes","give a summary of changes from GF 2.9"),
       ("coding","give advice on character encoding"),
       ("full","give full information of the commands"),
       ("license","show copyright and license information")
       ],
     exec = \opts ts -> 
       let
        msg = case ts of
          _ | isOpt "changes" opts -> changesMsg
          _ | isOpt "coding" opts -> codingMsg
          _ | isOpt "license" opts -> licenseMsg
          [t] -> let co = getCommandOp (showTree t) in 
                 case lookCommand co (allCommands cod pgf) of   ---- new map ??!!
                   Just info -> commandHelp True (co,info)
                   _ -> "command not found"
          _ -> commandHelpAll cod pgf opts
       in return (fromString msg) 
     }),
  ("i", emptyCommandInfo {
     longname = "import",
     synopsis = "import a grammar from source code or compiled .pgf file",
     explanation = unlines [
       "Reads a grammar from File and compiles it into a GF runtime grammar.",
       "If a grammar with the same concrete name is already in the state",
       "it is overwritten - but only if compilation succeeds.",
       "The grammar parser depends on the file name suffix:",
       "  .gf    normal GF source",
       "  .gfo   compiled GF source",
       "  .pgf   precompiled grammar in Portable Grammar Format"
       ],
     options = [ 
       -- ["prob", "retain", "gfo", "src", "no-cpu", "cpu", "quiet", "verbose"]
       ("retain","retain operations (used for cc command)"),
       ("src",   "force compilation from source"),
       ("v",     "be verbose - show intermediate status information")
       ]
     }),
  ("l", emptyCommandInfo {
     longname = "linearize",
     synopsis = "convert an abstract syntax expression to string",
     explanation = unlines [
       "Shows the linearization of a Tree by the grammars in scope.",
       "The -lang flag can be used to restrict this to fewer languages.",
       "A sequence of string operations (see command ps) can be given",
       "as options, and works then like a pipe to the ps command, except",
       "that it only affect the strings, not e.g. the table labels.",
       "These can be given separately to each language with the unlexer flag",
       "whose results are prepended to the other lexer flags. The value of the",
       "unlexer flag is a space-separated list of comma-separated string operation",
       "sequences; see example."
       ],
     examples = [
       "l -langs=LangSwe,LangNor no_Utt   -- linearize tree to LangSwe and LangNor",
       "gr -lang=LangHin -cat=Cl | l -table -to_devanagari -to_utf8 -- hindi table",
       "l -unlexer=\"LangSwe=to_utf8 LangHin=to_devanagari,to_utf8\" -- different lexers"
       ],
     exec = \opts -> return . fromStrings . map (optLin opts),
     options = [
       ("all","show all forms and variants"),
       ("multi","linearize to all languages (default)"),
       ("record","show source-code-like record"),
       ("table","show all forms labelled by parameters"),
       ("term", "show PGF term"),
       ("treebank","show the tree and tag linearizations with language names")
       ] ++ stringOpOptions,
     flags = [
       ("lang","the languages of linearization (comma-separated, no spaces)"),
       ("unlexer","set unlexers separately to each language (space-separated)")
       ]
     }),
  ("ma", emptyCommandInfo {
     longname = "morpho_analyse",
     synopsis = "print the morphological analyses of all words in the string",
     explanation = unlines [
       "Prints all the analyses of space-separated words in the input string,",
       "using the morphological analyser of the actual grammar (see command pf)"
       ],
     exec  = \opts ->  
               return . fromString . unlines . 
               map prMorphoAnalysis . concatMap (morphos opts) . 
               concatMap words . toStrings
     }),

  ("mq", emptyCommandInfo {
     longname = "morpho_quiz",
     synopsis = "start a morphology quiz",
     exec = \opts _ -> do
         let lang = optLang opts
         let typ  = optType opts
         morphologyQuiz cod pgf lang typ
         return void,
     flags = [
       ("lang","language of the quiz"),
       ("cat","category of the quiz"),
       ("number","maximum number of questions")
       ] 
     }),

  ("p", emptyCommandInfo {
     longname = "parse",
     synopsis = "parse a string to abstract syntax expression",
     explanation = unlines [
       "Shows all trees returned by parsing a string in the grammars in scope.",
       "The -lang flag can be used to restrict this to fewer languages.",
       "The default start category can be overridden by the -cat flag.",
       "See also the ps command for lexing and character encoding."
       ],
     exec = \opts -> return . fromTrees . concatMap (par opts) . toStrings,
     flags = [
       ("cat","target category of parsing"),
       ("lang","the languages of parsing (comma-separated, no spaces)")
       ]
     }),
  ("pg", emptyCommandInfo { -----
     longname = "print_grammar",
     synopsis = "print the actual grammar with the given printer",
     explanation = unlines [
       "Prints the actual grammar, with all involved languages.", 
       "In some printers, this can be restricted to a subset of languages",
       "with the -lang=X,Y flag (comma-separated, no spaces).",
       "The -printer=P flag sets the format in which the grammar is printed.",
       "N.B.1 Since grammars are compiled when imported, this command",
       "generally shows a grammar that looks rather different from the source.",
       "N.B.2 This command is slightly obsolete: to produce different formats",
       "the batch compiler gfc is recommended, and has many more options."
       ],
     exec  = \opts _ -> return $ fromString $ prGrammar opts,
     flags = [
       --"cat",
       ("lang",   "select languages for the some options (default all languages)"),
       ("printer","select the printing format (see gfc --help)")
       ],
     options = [
       ("cats",   "show just the names of abstract syntax categories"),
       ("fullform", "print the fullform lexicon"),
       ("missing","show just the names of functions that have no linearization")
       ]
     }),
  ("ph", emptyCommandInfo {
     longname = "print_history",
     synopsis = "print command history",
     explanation = unlines [
       "Prints the commands issued during the GF session.",
       "The result is readable by the eh command.", 
       "The result can be used as a script when starting GF."
       ],
     examples = [
      "ph | wf -file=foo.gfs  -- save the history into a file"
      ]
     }),
  ("ps", emptyCommandInfo {
     longname = "put_string",
     syntax = "ps OPT? STRING",
     synopsis = "return a string, possibly processed with a function",
     explanation = unlines [
       "Returns a string obtained from its argument string by applying",
       "string processing functions in the order given in the command line",
       "option list. Thus 'ps -f -g s' returns g (f s). Typical string processors",
       "are lexers and unlexers, but also character encoding conversions are possible.",
       "The unlexers preserve the division of their input to lines.",
       "To see transliteration tables, use command ut." 
       ], 
     examples = [
       "l (EAdd 3 4) | ps -code              -- linearize code-like output",
       "ps -lexer=code | p -cat=Exp          -- parse code-like input",
       "gr -cat=QCl | l | ps -bind -to_utf8  -- linearization output from LangFin", 
       "ps -from_utf8 \"jag ?r h?r\" | p       -- parser in LangSwe in UTF8 terminal",
       "ps -to_devanagari -to_utf8 \"A-p\"     -- show Devanagari in UTF8 terminal"
       ],
     exec = \opts -> return . fromString . stringOps (map prOpt opts) . toString,
     options = stringOpOptions
     }),
  ("pt", emptyCommandInfo {
     longname = "put_tree",
     syntax = "ps OPT? TREE",
     synopsis = "return a tree, possibly processed with a function",
     explanation = unlines [
       "Returns a tree obtained from its argument tree by applying",
       "tree processing functions in the order given in the command line",
       "option list. Thus 'pt -f -g s' returns g (f s). Typical tree processors",
       "are type checking and semantic computation."
       ], 
     examples = [
       "pt -compute (plus one two)   -- compute value",
       "p \"foo\" | pt -typecheck      -- type check parse results"
       ],
     exec = \opts -> return . fromTrees . treeOps (map prOpt opts),
     options = treeOpOptions pgf
     }),
  ("q",  emptyCommandInfo {
     longname = "quit",
     synopsis = "exit GF interpreter"
     }),
  ("rf",  emptyCommandInfo {
     longname = "read_file",
     synopsis = "read string or tree input from a file",
     explanation = unlines [
       "Reads input from file. The filename must be in double quotes.",
       "The input is interpreted as a string by default, and can hence be",
       "piped e.g. to the parse command. The option -tree interprets the",
       "input as a tree, which can be given e.g. to the linearize command.",
       "The option -lines will result in a list of strings or trees, one by line." 
       ],
     options = [
       ("lines","return the list of lines, instead of the singleton of all contents"),
       ("tree","convert strings into trees")
       ],
     exec = \opts arg -> do 
       let file = valStrOpts "file" "_gftmp" opts
       s <- readFile file
       return $ case opts of
         _ | isOpt "lines" opts && isOpt "tree" opts -> 
               fromTrees [t | l <- lines s, Just t <- [readTree l]] 
         _ | isOpt "tree" opts -> 
               fromTrees [t | Just t <- [readTree s]] 
         _ | isOpt "lines" opts -> fromStrings $ lines s 
         _ -> fromString s,
     flags = [("file","the input file name")] 
     }),
  ("tq", emptyCommandInfo {
     longname = "translation_quiz",
     synopsis = "start a translation quiz",
     exec = \opts _ -> do
         let from = valCIdOpts "from" (optLang opts) opts
         let to   = valCIdOpts "to"   (optLang opts) opts
         let typ  = optType opts
         translationQuiz cod pgf from to typ
         return void,
     flags = [
       ("from","translate from this language"),
       ("to","translate to this language"),
       ("cat","translate in this category"),
       ("number","the maximum number of questions")
       ] 
     }),
  ("se", emptyCommandInfo {
     longname = "set_encoding",
     synopsis = "set the encoding used in current terminal",
     syntax   = "se ID",
     examples = [
      "se cp1251 -- set encoding to cp1521",
      "se utf8   -- set encoding to utf8 (default)"
      ]
    }),
  ("sp", emptyCommandInfo {
     longname = "system_pipe",
     synopsis = "send argument to a system command",
     syntax   = "sp -command=\"SYSTEMCOMMAND\" STRING",
     exec = \opts arg -> do
       let tmpi = "_tmpi" ---
       let tmpo = "_tmpo"
       writeFile tmpi $ enc $ toString arg
       let syst = optComm opts ++ " " ++ tmpi
       system $ syst ++ " <" ++ tmpi ++ " >" ++ tmpo 
       s <- readFile tmpo
       return $ fromString s,
     flags = [
       ("command","the system command applied to the argument")
       ],
     examples = [
       "ps -command=\"wc\" \"foo\"",
       "gt | l | sp -command=\"grep \\\"who\\\"\" | sp -command=\"wc\""
       ]
     }),
  ("ut", emptyCommandInfo {
     longname = "unicode_table",
     synopsis = "show a transliteration table for a unicode character set",
     exec = \opts arg -> do
         let t = concatMap prOpt (take 1 opts)
         let out = maybe "no such transliteration" characterTable $ transliteration t
         return $ fromString out,
     options = [
       ("arabic",    "Arabic"),
       ("devanagari","Devanagari"),
       ("telugu",    "Telugu"),
       ("thai",      "Thai")
       ] 
     }),
  ("vt", emptyCommandInfo {
     longname = "visualize_tree",
     synopsis = "show a set of trees graphically",
     explanation = unlines [
       "Prints a set of trees in the .dot format (the graphviz format).",
       "The graph can be saved in a file by the wf command as usual.",
       "If the -view flag is defined, the graph is saved in a temporary file",
       "which is processed by graphviz and displayed by the program indicated",
       "by the flag. The target format is postscript, unless overridden by the",
       "flag -format."
       ],
     exec = \opts ts -> do
         let funs = not (isOpt "nofun" opts)
         let cats = not (isOpt "nocat" opts)
         let grph = visualizeTrees pgf (funs,cats) ts -- True=digraph
         if isFlag "view" opts || isFlag "format" opts then do
           let file s = "_grph." ++ s
           let view = optViewGraph opts ++ " "
           let format = optViewFormat opts 
           writeFile (file "dot") (enc grph)
           system $ "dot -T" ++ format ++ " " ++ file "dot" ++ " > " ++ file format ++ 
                    " ; " ++ view ++ file format
           return void
          else return $ fromString grph,
     examples = [
       "p \"hello\" | vt              -- parse a string and show trees as graph script",
       "p \"hello\" | vt -view=\"open\" -- parse a string and display trees on a Mac"
       ],
     options = [
       ("nofun","don't show functions but only categories"),
       ("nocat","don't show categories but only functions")
       ],
     flags = [
       ("format","format of the visualization file (default \"ps\")"),
       ("view","program to open the resulting file (default \"gv\")")
       ] 
     }),
  ("wf", emptyCommandInfo {
     longname = "write_file",
     synopsis = "send string or tree to a file",
     exec = \opts arg -> do
         let file = valStrOpts "file" "_gftmp" opts
         if isOpt "append" opts 
           then appendFile file (enc (toString arg))
           else writeFile file (enc (toString arg))
         return void,
     options = [
       ("append","append to file, instead of overwriting it")
       ],
     flags = [("file","the output filename")] 
     })
  ]
 where
   enc = encodeUnicode cod
   lin opts t = unlines [linearize pgf lang t    | lang <- optLangs opts]
   par opts s = concat  [parse pgf lang (optType opts) s | lang <- optLangs opts, canParse pgf lang]
 
   void = ([],[])

   optLin opts t = case opts of 
     _ | isOpt "treebank" opts -> treebank opts t
     _ -> unlines [linear opts lang t | lang <- optLangs opts] 
    
   linear opts lang = let unl = unlex opts lang in case opts of
       _ | isOpt "all"    opts -> allLinearize unl pgf lang
       _ | isOpt "table"  opts -> tableLinearize unl pgf lang
       _ | isOpt "term"   opts -> termLinearize pgf lang
       _ | isOpt "record" opts -> recordLinearize pgf lang
       _  -> unl . linearize pgf lang

   treebank opts t = unlines $ 
     (prCId (abstractName pgf) ++ ": " ++ showTree t) :
     [prCId lang ++ ": " ++ linear opts lang t | lang <- optLangs opts]

   unlex opts lang = stringOps (getUnlex opts lang ++ map prOpt opts)

   getUnlex opts lang = case words (valStrOpts "unlexer" "" opts) of
     lexs -> case lookup lang 
               [(mkCId la,tail le) | lex <- lexs, let (la,le) = span (/='=') lex, not (null le)] of
       Just le -> chunks ',' le
       _ -> []

-- Proposed logic of coding in unlexing:
--   - If lang has no coding flag, or -to_utf8 is not in opts, just opts are used.
--   - If lang has flag coding=utf8, -to_utf8 is ignored.
--   - If lang has coding=other, and -to_utf8 is in opts, from_other is applied first.
-- THIS DOES NOT WORK UNFORTUNATELY - can't use the grammar flag properly
   unlexx opts lang = {- trace (unwords optsC) $ -} stringOps optsC where
     optsC = case lookFlag pgf lang "coding" of
       Just "utf8" -> filter (/="to_utf8") $ map prOpt opts
       Just other | isOpt "to_utf8" opts -> 
                      let cod = ("from_" ++ other) 
                      in cod : filter (/=cod) (map prOpt opts)
       _ -> map prOpt opts

   optRestricted opts = 
     restrictPGF (\f -> and [hasLin pgf la f | la <- optLangs opts]) pgf

   optLangs opts = case valStrOpts "lang" "" opts of
     "" -> languages pgf
     lang -> map mkCId (chunks ',' lang)
   optLang opts = head $ optLangs opts ++ [wildCId]
   optType opts = 
     let str = valStrOpts "cat" (lookStartCat pgf) opts
     in case readType str of
          Just ty -> ty
          Nothing -> error ("Can't parse '"++str++"' as type")
   optComm opts = valStrOpts "command" "" opts
   optViewFormat opts = valStrOpts "format" "ps" opts
   optViewGraph opts = valStrOpts "view" "gv" opts
   optNum opts = valIntOpts "number" 1 opts
   optNumInf opts = valIntOpts "number" 1000000000 opts ---- 10^9

   fromTrees ts = (ts,unlines (map showTree ts))
   fromStrings ss = (map (Lit . LStr) ss, unlines ss)
   fromString  s  = ([Lit (LStr s)], s)
   toStrings = map showAsString 
   toString = unwords . toStrings

   prGrammar opts = case opts of
     _ | isOpt "cats" opts -> unwords $ map prCId $ categories pgf
     _ | isOpt "fullform" opts -> concatMap 
          (prFullFormLexicon . buildMorpho pgf) $ optLangs opts
     _ | isOpt "missing" opts -> 
           unlines $ [unwords (prCId la:":": map prCId cs) | 
                       la <- optLangs opts, let cs = missingLins pgf la]
     _ -> case valStrOpts "printer" "pgf" opts of
       v -> concatMap snd $ exportPGF noOptions (read v) pgf

   morphos opts s = 
     [lookupMorpho (buildMorpho pgf la) s | la <- optLangs opts]

   -- ps -f -g s returns g (f s)
   stringOps opts s = foldr app s (reverse opts) where
     app f = maybe id id (stringOp f) 

   treeOps opts s = foldr app s (reverse opts) where
     app f = maybe id id (treeOp pgf f) 

   showAsString t = case t of
     Lit (LStr s) -> s
     _ -> "\n" ++ showTree t  --- newline needed in other cases than the first

stringOpOptions = [
       ("bind","bind tokens separated by Prelude.BIND, i.e. &+"),
       ("chars","lexer that makes every non-space character a token"),
       ("from_cp1251","decode from cp1251 (Cyrillic used in Bulgarian resource)"),
       ("from_arabic","from unicode to GF Arabic transliteration"),
       ("from_devanagari","from unicode to GF Devanagari transliteration"),
       ("from_thai","from unicode to GF Telugu transliteration"),
       ("from_thai","from unicode to GF Thai transliteration"),
       ("from_utf8","decode from utf8"),
       ("lextext","text-like lexer"),
       ("lexcode","code-like lexer"),
       ("lexmixed","mixture of text and code (code between $...$)"), 
       ("to_cp1251","encode to cp1251 (Cyrillic used in Bulgarian resource)"),
       ("to_arabic","from GF Arabic transliteration to unicode"),
       ("to_devanagari","from GF Devanagari transliteration to unicode"),
       ("to_html","wrap in a html file with linebreaks"),
       ("to_telugu","from GF Telugu transliteration to unicode"),
       ("to_thai","from GF Thai transliteration to unicode"),
       ("to_utf8","encode to utf8"),
       ("unlextext","text-like unlexer"),
       ("unlexcode","code-like unlexer"),
       ("unlexmixed","mixture of text and code (code between $...$)"), 
       ("unchars","unlexer that puts no spaces between tokens"),
       ("unwords","unlexer that puts a single space between tokens (default)"),
       ("words","lexer that assumes tokens separated by spaces (default)")
       ]

treeOpOptions pgf = [(op,expl) | (op,(expl,_)) <- allTreeOps pgf]

translationQuiz :: String -> PGF -> Language -> Language -> Type -> IO ()
translationQuiz cod pgf ig og typ = do
  tts <- translationList pgf ig og typ infinity
  mkQuiz cod "Welcome to GF Translation Quiz." tts

morphologyQuiz :: String -> PGF -> Language -> Type -> IO ()
morphologyQuiz cod pgf ig typ = do
  tts <- morphologyList pgf ig typ infinity
  mkQuiz cod "Welcome to GF Morphology Quiz." tts

-- | the maximal number of precompiled quiz problems
infinity :: Int
infinity = 256

lookFlag :: PGF -> String -> String -> Maybe String
lookFlag pgf lang flag = lookConcrFlag pgf (mkCId lang) (mkCId flag)


