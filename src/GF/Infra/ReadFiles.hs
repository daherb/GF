module ReadFiles 
--- where 

--
(
--  
getAllFiles,fixNewlines,ModName,getOptionsFromFile,
--  
gfcFile,gfFile,gfrFile,isGFC,resModName,isOldFile) where

import Arch (selectLater, modifiedFiles, ModTime, getModTime,laterModTime)

import Option
import Operations
import UseIO
import System
import Char
import Monad
import List

-- make analysis for GF grammar modules. AR 11/6/2003--24/2/2004

-- to find all files that have to be read, put them in dependency order, and
-- decide which files need recompilation. Name file.gf is returned for them,
-- and file.gfc or file.gfr otherwise.

type ModName = String
type ModEnv  = [(ModName,ModTime)]

getAllFiles :: Options -> [InitPath] -> ModEnv -> FileName -> IOE [FullPath]
getAllFiles opts ps env file = do

  -- read module headers from all files recursively
  ds0  <- getImports ps file
  let ds = [((snd m,map fst ms),p) | ((m,ms),p) <- ds0]
  ioeIO $ putStrLn $ "all modules:" +++ show (map (fst . fst) ds)

    -- get a topological sorting of files: returns file names --- deletes paths
  ds1 <- ioeErr $ either 
           return 
           (\ms -> Bad $ "circular modules" +++ 
                     unwords (map show (head ms))) $ topoTest $ map fst ds

  -- associate each file name with its path --- more optimal: save paths in ds1
  let paths = [(f,p) | ((f,_),p) <- ds]
  let pds1 = [(p,f) | f <- ds1, Just p <- [lookup f paths]]
  if oElem fromSource opts 
    then return [gfFile (prefixPathName p f) | (p,f) <- pds1]
    else do


    ds2 <- ioeIO $ mapM (selectFormat env) pds1

    let ds4 = needCompile opts (map fst ds0) ds2
    return ds4

-- to decide whether to read gf or gfc, or if in env; returns full file path

data CompStatus =
   CSComp -- compile: read gf
 | CSRead -- read gfc
 | CSEnv  -- gfc is in env
 | CSEnvR -- also gfr is in env
 | CSDont -- don't read at all
 | CSRes  -- read gfr
  deriving (Eq,Show)

selectFormat :: ModEnv -> (InitPath,ModName) -> IO (ModName,(InitPath,CompStatus))
selectFormat env (p,f) = do
  let pf = prefixPathName p f
  let mtenv = lookup f env   -- Nothing if f is not in env
  let rtenv = lookup (resModName f) env
  mtgfc <- getModTime $ gfcFile pf
  mtgf  <- getModTime $ gfFile pf
  let stat = case (rtenv,mtenv,mtgfc,mtgf) of
        (Just tenv,_,_,Just tgf) | laterModTime tenv tgf -> CSEnvR
        (_,Just tenv,_,Just tgf) | laterModTime tenv tgf -> CSEnv
        (_,_,Just tgfc,Just tgf) | laterModTime tgfc tgf -> CSRead
        _ -> CSComp
  return $ (f, (p,stat))


needCompile :: Options -> 
               [ModuleHeader] -> [(ModName,(InitPath,CompStatus))] -> [FullPath]
needCompile opts headers sfiles0 = paths $ res $ mark $ iter changed where

  deps = [(snd m,map fst ms) | (m,ms) <- headers]
  typ m = maybe MTyOther id $ lookup m [(m,t) | ((t,m),_) <- headers]
  uses m = [(n,u) | ((_,n),ms) <- headers, (k,u) <- ms, k==m]
  stat0 m = maybe CSComp snd $ lookup m sfiles0

  allDeps = [(m,iterFix add ms) | (m,ms) <- deps] where
    add os = [m | o <- os, Just n <- [lookup o deps],m <- n]

  -- only treat reused, interface, or instantiation if needed
  sfiles = map relevant sfiles0
  relevant fp@(f,(p,st)) = 
    let us = uses f in
    if not (all noComp us) then
      fp else 
    if (elem (typ f) [MTyIncomplete, MTyIncResource] || 
        (not (null us) && all isAux us)) then
      (f,(p,CSDont)) else
      fp

  isAux = flip elem [MUReuse,MUInstance,MUComplete] . snd
  noComp = flip elem [CSRead,CSEnv,CSEnvR] . stat0 . fst

  -- start with the changed files themselves; returns [ModName]
  changed = [f | (f,(_,CSComp)) <- sfiles] 

  -- add other files that depend on some changed file; returns [ModName]
  iter np = let new = [f | (f,fs) <- deps, 
                           not (elem f np), any (flip elem np) fs]
            in  if null new then np else (iter (new ++ np))

  -- for each module in the full list, compile if depends on what needs compile
  -- returns [FullPath]
  mark cs = [(f,(path,st)) | 
                (f,(path,st0)) <- sfiles, 
                let st = if (elem f cs) then CSComp else st0]

  -- if a compilable file depends on a resource, read gfr instead of gfc/env
  -- but don't read gfr if already in env (by CSEnvR)
  -- Also read res if the option "retain" is present
  res cs = map mkRes cs where
    mkRes x@(f,(path,st)) | elem st [CSRead,CSEnv] = case typ f of
      t | elem t [MTyResource,MTyIncResource] &&
          not (null [m | (m,(_,CSComp)) <- cs,
                                   Just ms <- [lookup m allDeps], elem f ms])
                    || oElem retainOpers opts
        -> (f,(path,CSRes))
      _ -> x
    mkRes x = x

  -- construct list of paths to read
  paths cs = [mkName f p st | (f,(p,st)) <- cs, elem st [CSComp, CSRead,CSRes]]

  mkName f p st = mk $ prefixPathName p f where
    mk = case st of
      CSComp -> gfFile
      CSRead -> gfcFile
      CSRes  -> gfrFile

isGFC = (== "gfc") . fileSuffix

gfcFile = suffixFile "gfc"
gfrFile = suffixFile "gfr"
gfFile  = suffixFile "gf"

resModName = ('#':)

-- to get imports without parsing the whole files

getImports :: [InitPath] -> FileName -> IOE [(ModuleHeader,InitPath)]
getImports ps = get [] where
  get ds file = do
    let name = fileBody file
    (p,s) <- readFileIfPath ps $ file
    let ((typ,mname),imps) = importsOfFile s
    ioeErr $ testErr  (mname == name) $ 
             "module name differs from file name in" +++ name
    case imps of
      _ | elem name (map (snd . fst . fst) ds) -> return ds  --- file already read
      [] -> return $ (((typ,name),[]),p):ds
      _ -> do
        let files = map (gfFile . fst) imps --- requires there's always .gf file
        foldM get ((((typ,name),imps),p):ds) files

-- internal module dep information

data ModUse =
   MUReuse
 | MUInstance
 | MUComplete
 | MUOther
  deriving (Eq,Show)

data ModTyp =
   MTyResource
 | MTyIncomplete
 | MTyIncResource -- interface, incomplete resource
 | MTyOther
  deriving (Eq,Show)

type ModuleHeader = ((ModTyp,ModName),[(ModName,ModUse)])

importsOfFile :: String -> ModuleHeader
importsOfFile = 
  getModuleHeader .          -- analyse into mod header
  filter (not . spec) .      -- ignore keywords and special symbols
  unqual .                   -- take away qualifiers
  unrestr .                  -- take away union restrictions
  takeWhile (not . term) .   -- read until curly or semic
  lexs .                     -- analyse into lexical tokens
  unComm                     -- ignore comments before the headed line
 where
    term = flip elem ["{",";"]
    spec = flip elem ["of", "open","in",":", "->","=", "(", ")",",","**","union"]
    unqual ws = case ws of
      "(":q:ws' -> unqual ws'
      w:ws' -> w:unqual ws'
      _ -> ws
    unrestr ws = case ws of
      "[":ws' -> unrestr $ tail $ dropWhile (/="]") ws'
      w:ws' -> w:unrestr ws'
      _ -> ws

getModuleHeader :: [String] -> ModuleHeader -- with, reuse
getModuleHeader ws = case ws of
  "incomplete":ws2 -> let ((ty,name),us) = getModuleHeader ws2 in
    case ty of
      MTyResource -> ((MTyIncResource,name),us)
      _ -> ((MTyIncomplete,name),us)
  "interface":ws2 -> let ((_,name),us) = getModuleHeader ("resource":ws2) in
    ((MTyIncResource,name),us)
 
  "resource":name:ws2 -> case ws2 of
    "reuse":m:_ -> ((MTyResource,name),[(m,MUReuse)])
    m:"with":ms -> ((MTyResource,name),(m,MUOther):[(n,MUComplete) | n <- ms])
    ms -> ((MTyResource,name),[(n,MUOther) | n <- ms])

  "instance":name:m:ws2 -> case ws2 of
    "reuse":n:_ -> ((MTyResource,name),(m,MUInstance):[(n,MUReuse)])
    n:"with":ms -> 
      ((MTyResource,name),(m,MUInstance):(n,MUComplete):[(n,MUOther) | n <- ms])
    ms -> ((MTyResource,name),(m,MUInstance):[(n,MUOther) | n <- ms])

  _:name:ws2 -> case ws2 of
    "reuse":m:_ -> ((MTyOther,name),[(m,MUReuse)])
    m:n:"with":ms -> 
      ((MTyOther,name),(m,MUInstance):(n,MUOther):[(n,MUComplete) | n <- ms])
    m:"with":ms -> ((MTyOther,name),(m,MUOther):[(n,MUComplete) | n <- ms])
    ms -> ((MTyOther,name),[(n,MUOther) | n <- ms])

unComm s = case s of
      '-':'-':cs -> unComm $ dropWhile (/='\n') cs
      '{':'-':cs -> dpComm cs
      c:cs -> c : unComm cs
      _ -> s
    
dpComm s = case s of
      '-':'}':cs -> unComm cs
      c:cs -> dpComm cs
      _ -> s
    
lexs s = x:xs where 
      (x,y) = head $ lex s
      xs = if null y then [] else lexs y

-- options can be passed to the compiler by comments in --#, in the main file
 
getOptionsFromFile ::  FilePath -> IO Options
getOptionsFromFile file = do
  s <- readFileIf file
  let ls = filter (isPrefixOf "--#") $ lines s
  return $ fst $ getOptions "-" $ map (unwords . words . drop 3) ls

-- check if old GF file
isOldFile :: FilePath -> IO Bool
isOldFile f = do
  s <- readFileIf f
  let s' = unComm s
  return $ not (null s') && old (head (words s'))
 where
   old = flip elem $ words 
     "cat category data def flags fun include lin lincat lindef lintype oper param pattern printname rule"



-- old GF tolerated newlines in quotes. No more supported!
fixNewlines s = case s of
     '"':cs -> '"':mk cs
     c  :cs -> c:fixNewlines cs
     _ -> s
 where
   mk s = case s of
     '\\':'"':cs -> '\\':'"': mk cs
     '"'     :cs -> '"' :fixNewlines cs
     '\n'    :cs -> '\\':'n': mk cs
     c       :cs -> c : mk cs
     _ -> s 

