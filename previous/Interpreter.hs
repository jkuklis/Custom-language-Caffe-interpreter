import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as M
import ErrM
import Text.Read hiding (Ident, lift, get)
import System.Environment
import System.IO

import AbsGrammar
import LexGrammar
import ParGrammar

data Result 
    = RInteger Integer 
    | RBool Bool 
    | RString String 
    | RTab Integer [Result] 
    | RVoid 
    | RStruct String (M.Map String Result) 
    | RBreak 
    | RCont 
    | RReturn Result 
    | RFun Env Type [Par] Block
    deriving (Eq, Ord)

data MType 
    = MType Type 
    | UType Type
    | NotYet 
    | Counter Integer  
    | MBreak MType 
    | MCont MType
    deriving (Show, Eq, Ord)


eq :: MType -> MType -> Bool
eq (UType t1) (MType t2) = t1 == t2
eq (MType t1) (UType t2) = t1 == t2
eq (NotYet) t2 = True
eq t1 (NotYet) = True
eq t1 t2 = t1 == t2 


stronger :: MType -> MType -> MType
stronger (UType t1) (UType t2) = UType t1
stronger (UType t1) (MType t2) = MType t2
stronger (MType t1) (UType t2) = MType t1
stronger (MType t1) (MType t2) = MType t1
stronger NotYet t2 = t2
stronger t1 NotYet = t1


firstYet :: MType -> MType -> MType
firstYet NotYet t2 = t2
firstYet t1 _ = t1


getTypes :: [Par] -> [Type] -> [Type]
getTypes [] li = reverse li
getTypes ((Param t id):ps) li = t : (getTypes ps li) 


instance Show Result where
    show (RInteger i) = show i
    show (RBool b) = show b
    show (RString s) = show s
    show (RTab size r) = show r
    show RVoid = "void"
    show (RStruct struct m) = 
        let repr = fmap (\(x,y) -> x ++ " = " ++ (show y) ++ ", ") (M.toList m)
        in struct ++ " {" ++ (concat repr) ++ "}"
    show RBreak = "break"
    show RCont = "cont"
    show (RReturn r) = "ret " ++ show r
    show (RFun e t par bl) = "fun"


data PDef 
    = SDef (M.Map String Type) 
    | VDef Loc
    deriving (Show, Eq, Ord)

type Context = M.Map Integer Result
type ContextT = M.Map Integer MType
type Env = M.Map String PDef
type Exception = String
type Log = [String]
type Loc = Integer


defVal :: Type -> Result
defVal Int = RInteger 0
defVal Str = RString ""
defVal Bool = RBool False
defVal Void = RVoid


eval :: Expr -> ExceptT Exception (RWS Env Log Context) Result
eval expr = case expr of
    ELitInt n           -> return $ RInteger n
    ELitTrue            -> return $ RBool True
    ELitFalse           -> return $ RBool False
    EString s           -> return $ RString s

    Paren e             -> eval e
    Not e               -> do
                            RBool b <- eval e;
                            return $ RBool $ not b

    Neg e               -> do
                            RInteger i <- eval e;
                            return $ RInteger (-i)

    StoI s              -> case readMaybe s :: Maybe Integer of
                                Just v -> return $ RInteger v
                                Nothing -> throwError $ "Failed to read Int from String: " ++ s

    ItoS s              -> return $ RString $ show s
    
    EAdd e1 op e2       -> do
                            RInteger i1 <- eval e1
                            RInteger i2 <- eval e2

                            case op of
                                Plus -> return $ RInteger $ i1 + i2
                                Minus -> return $ RInteger $ i1 - i2

    EMul e1 op e2       -> do
                            RInteger i1 <- eval e1
                            RInteger i2 <- eval e2

                            case op of
                                Times -> return $ RInteger $ i1 * i2
                                Div -> if i2 == 0
                                    then throwError "Divided by 0"
                                    else return $ RInteger $ i1 `div` i2
                                Mod -> if i2 == 0
                                    then throwError "Modulo by 0"
                                    else return $ RInteger $ i1 `mod` i2

    EVar (Ident x)      -> do
                            Just (VDef p) <- asks $ M.lookup x
                            Just r <- gets $ M.lookup p
                            return r


    ERel e1 op e2       -> do
                            v1 <- eval e1
                            v2 <- eval e2
                            case op of
                                LTo -> return $ RBool (v1 < v2)
                                LEo -> return $ RBool (v1 <= v2)
                                GTo -> return $ RBool (v1 > v2)
                                GEo -> return $ RBool (v1 >= v2)
                                EQo -> return $ RBool (v1 == v2)
                                NEo -> return $ RBool (v1 /= v2)

    EAnd e1 e2          -> do
                            RBool b1 <- eval e2
                            RBool b2 <- eval e2
                            return $ RBool $ b1 && b2

    EOr e1 e2           -> do
                            RBool b1 <- eval e2
                            RBool b2 <- eval e2
                            return $ RBool $ b1 || b2

    ETab t size         -> let retTab = \s x -> return $ RTab s $ replicate (fromIntegral s) x

                            in case size of
                                (s:[]) -> retTab s $ defVal t
                                (s:ss) -> do
                                   lr <- eval (ETab t ss)
                                   retTab s lr

    TableIni l          -> case l of
                            [] -> return $ RTab 0 []

                            (e:[]) -> do
                                re <- eval e
                                return $ RTab 1 [re]

                            (e:es) -> do
                                RTab size rl <- eval $ TableIni es
                                re <- eval e
                                return $ RTab (size + 1) $ re : rl
                            
    StructIni (Ident s) es 
                        -> case es of
                            [] -> return $ RStruct s M.empty

                            ((AtrInR (Ident s) e):es') -> do
                                re <- eval e
                                RStruct struct m <- eval $ StructIni (Ident s) es'
                                return $ RStruct s $ M.insert s re m

    ETabIndex (Ident s) l 
                        -> do
                            let
                                getFromTab t [] = Right t

                                getFromTab (RTab size r) (i:is) = 
                                    if i < size
                                        then getFromTab (r !! (fromIntegral i)) is
                                        else Left $ "Index out of reach: " ++ (show i) ++ " in " ++ s ++ ", max: " ++ (show size)

                            Just (VDef p) <- asks $ M.lookup s
                            Just t <- gets $ M.lookup p
                            let val = getFromTab t l
                            case val of
                                Right r -> return r
                                Left s -> throwError s
    

    EApp (Ident s) args -> do
                            Just (VDef pos) <- asks $ M.lookup s
                            Just (RFun fenv t argNames (Blck bl)) <- gets $ M.lookup pos                       
                            let
                                place [] [] env = do
                                    rr <- local (\e -> env) $ runStmt bl
                                    case rr of
                                        RReturn rr' -> return rr'
                                        RVoid -> return rr
    
                                place ((Param t (Ident x)):aN) (e:es) env = do
                                    re <- eval e
                                    Just (RInteger pos) <- gets $ M.lookup 0
                                    let env' = M.insert x (VDef pos) env
                                    let g = M.insert 0 $ RInteger $ pos + 1 
                                    modify $ (M.insert pos re) . g             
                                    place aN es env'

                            env <- ask                        
                            local (\e -> env) $ place argNames args fenv
                          

    ELambda t params st -> do
                            env <- ask
                            return $ RFun env t params $ Blck [st]
                        

    EAttrib (Attrib (Ident s) ids)
                        -> do
                            let getAtr m (Ident as : []) =
                                    let Just r = M.lookup as m
                                    in r

                                getAtr m (Ident as : aids) = 
                                    let Just (RStruct struct stru) = M.lookup as m
                                    in getAtr stru aids

                            Just (VDef p) <- asks $ M.lookup s
                            Just (RStruct struct m) <- gets $ M.lookup p
                            return $ getAtr m ids


runStmt :: [Stmt] -> ExceptT Exception (RWS Env Log Context) Result
runStmt [] = return RVoid
 
runStmt toRun@(stmt:stmts) =
    case stmt of
        Empty               -> runStmt stmts
        

        BStmt (Blck [])     -> runStmt stmts


        BStmt (Blck st)     -> do
                                env <- ask
                                val <- runStmt st
                                case val of
                                    RReturn _ -> return val
                                    _ -> local (\e -> env) $ runStmt stmts            


        Decl t []           -> runStmt stmts


        Decl t (d:ds)       -> let 
                                insert s v = do
                                    Just (RInteger pos) <- gets (M.lookup 0)
                                    let f = M.insert s $ VDef pos
                                    let g = M.insert 0 $ RInteger $ pos + 1 
                                    modify $ (M.insert pos v) . g              
                                    local f $ runStmt $ (Decl t ds) : stmts

                                in case d of
                                    Init (Ident s) e -> do
                                        r <- eval e
                                        insert s r

                                    NoInit (Ident s) -> do
                                        let val = defVal t
                                        insert s val


        Assign (Ident s) e  -> do
                                Just (VDef p) <- asks $ M.lookup s
                                val <- eval e
                                modify $ M.insert p val
                                runStmt stmts


        AssignAttr (Attrib (Ident s) ((Ident as) : ids)) e -> do
                                re <- eval e
                                Just (VDef p) <- asks $ M.lookup s
                                Just (RStruct id m) <- gets $ M.lookup p
                                modify $ M.insert p $ RStruct id (M.insert as re m)
                                runStmt stmts


        Change (Ident s) op e 
                            -> do
                                Just (VDef p) <- asks $ M.lookup s
                                Just (RInteger ro) <- gets $ M.lookup p
                                let f a = do
                                    modify $ M.insert p $ RInteger a
                                    runStmt stmts               
                                RInteger val <- eval e
                                case op of
                                    ChIncr -> f $ ro + val
                                    ChDecr -> f $ ro - val 
                                    ChMul -> f $ ro * val
                                    ChDiv -> f $ ro `div` val 
                                    ChMod -> f $ ro `mod` val


        -- unecessary big right now, as only one level of depth is allowed
        ChangeAttr (Attrib (Ident s) ids) op e 
                            -> do
                                Just (VDef pos) <- asks $ M.lookup s
                                Just (RStruct struct m) <- gets $ M.lookup pos
                                RInteger re <- eval e
                                let 
                                    modMap mm ((Ident as) : []) = do
                                        let Just (RInteger org) = M.lookup as mm

                                        let f a = M.insert as (RInteger a) mm              
                                        case op of
                                            ChIncr -> f $ org + re
                                            ChDecr -> f $ org - re
                                            ChMul -> f $ org * re
                                            ChDiv -> f $ org `div` re
                                            ChMod -> f $ org `mod` re
                                    
                                    modMap mm (Ident as : ids) = do
                                        let Just (RStruct struct am) = M.lookup as mm
                                        let am' = modMap mm ids
                                        M.insert as (RStruct struct am') mm

                                let m' = modMap m ids
                                modify $ M.insert pos $ RStruct struct m'

                                runStmt stmts 


        IncrDecr (Ident s) op 
                            -> do
                                Just (VDef p) <- asks $ M.lookup s
                                Just (RInteger i) <- gets $ M.lookup p
                                let f a = do
                                    modify $ M.insert p $ RInteger a
                                    runStmt stmts

                                case op of
                                    Incr -> f $ i + 1
                                    Decr -> f $ i - 1                  


        IncrDecrA (Attrib (Ident s) ids) op 
                            -> do
                                Just (VDef pos) <- asks $ M.lookup s
                                Just (RStruct struct m) <- gets $ M.lookup pos

                                let 
                                    modMap mm ((Ident as) : []) = do
                                        let Just (RInteger org) = M.lookup as mm
                                        let f a = M.insert as (RInteger a) mm              
                                        case op of
                                            Incr -> f $ org + 1
                                            Decr -> f $ org - 1
                                    
                                    modMap mm (Ident as : ids) = do
                                        let Just (RStruct struct am) = M.lookup as mm
                                        let am' = modMap mm ids
                                        M.insert as (RStruct struct am') mm

                                let m' = modMap m ids
                                modify $ M.insert pos $ RStruct struct m'

                                runStmt stmts 

        Ret e
                            -> do
                                val <- eval e
                                return $ RReturn val

        VRet                -> return $ RReturn RVoid

        Cond e st           -> do
                                RBool b <- eval e
                                if b
                                    then do
                                        env <- ask
                                        val <- runStmt [st]
                                        case val of
                                            RReturn _ -> return val
                                            _ -> local (\e -> env) $ runStmt stmts
                                    else runStmt stmts


        CondElse e st1 st2  -> do
                                RBool b <- eval e
                                if b
                                    then do
                                        env <- ask
                                        val <- runStmt [st1]
                                        case val of
                                            RReturn _ -> return val
                                            _ -> local (\e -> env) $ runStmt stmts
                                    else 
                                        runStmt $ st2 : stmts


        CondElif e st1 elifs st2 
                            -> do
                                case elifs of
                                    [] -> runStmt $ (CondElse e st1 st2) : stmts
                                    ((Elf e st):elfs) -> do
                                        RBool b <- eval e
                                        if b
                                            then do
                                                env <- ask
                                                val <- runStmt [st1]
                                                case val of
                                                    RReturn _ -> return val
                                                    _ -> local (\e -> env) $ runStmt stmts
                                            else
                                                runStmt $ (CondElif e st elfs st2) : stmts

    
        While e st          -> do
                                RBool b <- eval e
                                if b
                                    then do
                                        env <- ask
                                        val <- runStmt [st]
                                        case val of
                                            RReturn RCont -> local (\e -> env) $ runStmt toRun
                                            RReturn RBreak -> local (\e -> env) $ runStmt stmts

                                            RVoid -> local (\e -> env) $ runStmt toRun
                                            RReturn _ -> return val
                                            
                                    else
                                        runStmt stmts

    
        InDecl (FunDef t (Ident s) par bl)
                            -> do
                                Just (RInteger pos) <- gets $ M.lookup 0            
                                env <- ask
                                let env' = M.insert s (VDef pos) env

                                modify $ M.insert pos $ RFun env' t par bl
                                modify $ M.insert 0 $ RInteger $ pos + 1

                                local (\e -> env') $ runStmt stmts


        Eval e              -> do
                                eval e
                                runStmt stmts

        Break               -> return $ RReturn RBreak
        
        Cont                -> return $ RReturn RCont

        Print e             -> do
                                val <- eval e
                                tell [show val]
                                runStmt stmts

                    
     
interpret :: Prog -> ExceptT Exception (RWS Env Log Context) Integer
interpret (Program (def:defs)) = do                
    case def of
        FnDecl (FunDef t (Ident "main") args (Blck st)) 
                            -> do
                                RReturn (RInteger i) <- runStmt st
                                return i


        FnDecl (FunDef t (Ident s) args bl) 
                            -> do
                                Just (RInteger pos) <- gets $ M.lookup 0            
                                env <- ask
                                let env' = M.insert s (VDef pos) env

                                modify $ M.insert pos $ RFun env' t args bl
                                modify $ M.insert 0 $ RInteger $ pos + 1

                                local (\e -> env') $ interpret $ Program defs

    
        RecDef (Ident s) atr -> interpret $ Program defs


-- Types


evalT :: Expr -> ExceptT Exception (RWS Env Log ContextT) MType
evalT expr = case expr of

    ELitInt n           -> return $ MType Int
    ELitTrue            -> return $ MType Bool
    ELitFalse           -> return $ MType Bool
    EString s           -> return $ MType Str

    Paren e             -> evalT e

    Not e               -> do
                            te <- evalT e
                            case te of
                                MType Bool -> return te
                                _ -> throwError $ "Wrong not type: " ++ (show te)

    Neg e               -> do
                            te <- evalT e
                            case te of
                                MType Int -> return te
                                _ -> throwError $ "Wrong neg type: " ++ (show te)

    StoI s              -> return $ MType Int

    ItoS i              -> return $ MType Str
    
    EAdd e1 op e2       -> do
                            t1 <- evalT e1
                            t2 <- evalT e2
                            if t1 == MType Int && (t2 == MType Int)
                                then return $ MType Int
                                else throwError $ "Wrong add type: " ++ (show t1) ++ " or " ++ (show t2)

    EMul e1 op e2       -> do
                            t1 <- evalT e1
                            t2 <- evalT e2
                            if t1 == MType Int && (t2 == MType Int)
                                then return $ MType Int
                                else throwError $ "Wrong mul type: " ++ (show t1) ++ " or " ++ (show t2)
                            

    EVar (Ident x)      -> do
                            pos <- asks $ M.lookup x
                            case pos of
                                Just (VDef p) -> do
                                    Just m <- gets $ M.lookup p
                                    return m

                                _ -> throwError $ "No such identifier: " ++ x 

    ERel e1 op e2       -> do
                            t1 <- evalT e1
                            t2 <- evalT e2
                            if t1 == MType Int && (t2 == MType Int)
                                then return $ MType Bool
                                else throwError $ "Wrong rel type: " ++ (show t1) ++ " or " ++ (show t2)

    EAnd e1 e2          -> do
                            t1 <- evalT e1
                            t2 <- evalT e2
                            if t1 == MType Bool && (t2 == MType Bool)
                                then return $ MType Bool
                                else throwError $ "Wrong and types: " ++ (show t1) ++ " or " ++ (show t2)

    EOr e1 e2           -> do
                            t1 <- evalT e1
                            t2 <- evalT e2
                            if t1 == MType Bool && (t2 == MType Bool)
                                then return $ MType Bool
                                else throwError $ "Wrong or types: " ++ (show t1) ++ " or " ++ (show t2)

    ETab t size         -> case size of
                               (s:[]) -> return $ MType $ Tab t
                               (s:ss) -> do
                                       MType tt <- evalT (ETab t ss)
                                       return $ MType $ Tab tt

    TableIni l          -> let 
                            helper t l = 
                                case l of
                                    [] -> return $ MType $ Tab Void

                                    (e:[]) -> do
                                        te@(MType rte) <- evalT e
                                        if te /= NotYet && (eq t te)
                                            then return $ MType $ Tab rte
                                            else throwError $ "Wrong type in table ini: " ++ (show te) ++ " instead of " ++ (show t)

                                    (e:es) -> do
                                        te <- evalT e
                                        if te /= NotYet && (eq t te)
                                            then helper te es
                                            else throwError $ "Wrong type in table ini: " ++ (show te) ++ " instead of " ++ (show t)

                            in helper NotYet l
                        
    
    StructIni (Ident stru) es -> do
                            str <- asks $ M.lookup stru
                            case str of
                                Just (SDef sm) -> do
                                    env <- ask
                                    state <- get
                                    let 
                                        f [] already = 
                                            if length already == (M.size sm) 
                                                then Right ""
                                                else Left $ "Initialization list in structini too short for: " ++ stru

                                        f ((AtrInR (Ident s) e):es') alr =
                                            if elem s alr
                                                then Left $ "Double attribute in structini: " ++ s ++ " for " ++ stru
                                                else do
                                                    let (jre,_,_) = runRWS (runExceptT (evalT e)) env state
                                                    case jre of
                                                        Right re ->
                                                            case M.lookup s sm of
                                                                Just ts -> 
                                                                    if MType ts == re
                                                                        then f es' (s:alr)
                                                                    else Left $ "Wrong type for attribute: " ++ (show ts) ++ " instead of " ++ (show re) ++ " for " ++ s ++ " in " ++ stru  
                                                                _ -> Left $ "No such attribute: " ++ s ++ " in struct " ++ stru
                                                        Left s -> Left s

                                    case f es [] of
                                        Right _ -> return $ MType $ Struct (Ident stru)
                                        Left s -> throwError s

                                _ -> throwError $ "No such struct for structini: " ++ stru

                            
    ETabIndex (Ident s) l -> do
                            let 
                                getTypeFromTab t [] = Right t
                                getTypeFromTab (Tab t) (lh:lt) = getTypeFromTab t lt
                                getTypeFromTab _ (lh:lt) = Left $ "Too deep into tab: " ++ s

                            pos <- asks $ M.lookup s

                            case pos of
                                Just (VDef p) -> do

                                    Just (MType t) <- gets $ M.lookup p
                                    case getTypeFromTab t l of
                                        Right t -> return $ MType t
                                        Left s -> throwError s
                                        
                                _ -> throwError $ "No such tab: " ++ s
    

    EApp (Ident s) args -> do
                            jp <- asks $ M.lookup s
                            case jp of                    
                                Just (VDef pos) -> do
                                    jf <- gets $ M.lookup pos
                                    case jf of
                                        Just (MType (Fun t targs)) -> do 
                                            let
                                                place [] [] = return $ MType t

                                                place (t:ta) (e:es) = do
                                                    re <- evalT e
                                                    
                                                    if MType t == re then           
                                                        place ta es
                                                    
                                                    else throwError $ "Wrong argument type: " ++ (show re) ++ " instead of " ++ (show t)

                                            if length targs == (length args) then do 
                                              
                                                env <- ask                        
                                                local (\e -> env) $ place targs args

                                            else throwError $ "Wrong number of arguments" ++ (show (length targs))

                                        Just t -> throwError $ "Wrong type, instead of function: " ++ (show t)

                                _ -> throwError $ "Undefined function: " ++ (show s)
                          

    ELambda t params st -> let
                                place [] = do
                                    res <- runStmtT NotYet [st]
                                    return res

                                place ((Param t (Ident x)):aN) = do

                                    Just (Counter pos) <- gets $ M.lookup 0

                                    modify $ M.insert pos $ MType t
                                    modify $ M.insert 0 $ Counter $ pos + 1                            

                                    let f = M.insert x $ VDef pos
                                    
                                    local f $ place aN
                        
                            in do
                                env <- ask
                
                                res <- local (\e -> env) $ place params

                                if (res == MType t) || (t == Void && res == NotYet) 
                                    then return $ MType $ Fun t $ getTypes params []
                                    else throwError $ "Wrong return type: " ++ (show res) ++ " instead of " ++ (show t)
                            

    EAttrib (Attrib (Ident s) ids)
                        -> do
                            let 
                                getAtrType m (Ident as:[]) =
                                    case M.lookup as m of
                                        Just t -> Right t
                                        _ -> Left $ "No such identifier: " ++ as
                                
                                getAtrType m _ = Left $ "Too deep into struct"

                            jp <- asks $ M.lookup s
                            case jp of
                                Just (VDef p) -> do
                                    js <- gets $ M.lookup p
                                    case js of
                                        Just (MType (Struct (Ident stru))) -> do
                                            jstr <- asks $ M.lookup stru
                                            case jstr of 
                                                Just (SDef sm) ->
                                                    case getAtrType sm ids of
                                                        Right t -> return $ MType t
                                                        Left s -> throwError s

                                                _ -> throwError $ "No such struct: " ++ stru                                   

                                        _ -> throwError $ "Not a struct instance: " ++ s

                                _ -> throwError $ "No such struct instance: " ++ s



runStmtT :: MType -> [Stmt] -> ExceptT Exception (RWS Env Log ContextT) MType
runStmtT ret [] = return ret
 
runStmtT ret (stmt:stmts) = do          
    case stmt of
        Empty               -> runStmtT ret stmts
        
        BStmt (Blck [])     -> runStmtT ret stmts

        BStmt (Blck st)     -> do
                                env <- ask
                                val <- runStmtT ret st
                                let cont ret = local (\e -> env) $ runStmtT ret stmts
                                case ret of
                                    NotYet -> cont val
                                    _ -> 
                                        if eq val ret
                                            then cont $ stronger ret val
                                            else throwError "Different return type in block"           

        Decl t []           -> runStmtT ret stmts

        Decl t (d:ds)       -> do 
                                let insert s v = do
                                    Just (Counter pos) <- gets $ M.lookup 0
                                    let f = M.insert s $ VDef pos
                                    let g = M.insert 0 $ Counter $ pos + 1
                                    modify $ (M.insert pos v) . g              
                                    local f $ runStmtT ret $ (Decl t ds) : stmts  
                                
                                case d of
                                    Init (Ident s) e -> do
                                        r <- evalT e
                                        if r == MType t 
                                            then insert s r
                                            else throwError $ "Wrong type in declaration: " ++ (show r) ++ " instead of " ++ (show t) ++ " for " ++ s
                            
                                    NoInit (Ident s) -> do
                                        if (elem t [Int, Str, Bool, Void])
                                            then insert s $ MType t
                                            else throwError $ "No default value for type: " ++ (show t) ++ " in decl of " ++ s


        Assign (Ident s) e  -> do
                                pos <- asks $ M.lookup s
                                case pos of
                                    Just (VDef p) -> do
                                        val <- evalT e
                                        Just t <- gets $ M.lookup p

                                        if val == t
                                            then runStmtT ret stmts
                                            else throwError $ "Wrong type in assignment: " ++ (show val) ++ " instead of " ++ (show t) ++ " for " ++ s

                                    _ -> throwError $ "No such identifier in assignment: " ++ s            

        
        AssignAttr (Attrib (Ident s) ((Ident as) : ids)) e 
                            -> do
                                te <- evalT e
                                pos <- asks $ M.lookup s

                                case pos of
                                    Just (VDef p) -> do
                                        jm <- gets $ M.lookup p

                                        case jm of
                                            Just (MType (Struct (Ident ss))) -> do
                                                jsd <- asks $ M.lookup ss

                                                case jsd of
                                                    Just (SDef m) ->

                                                        case M.lookup as m of
                                                            Just t -> if MType t == te
                                                                then runStmtT ret stmts
                                                                else throwError $ "Wrong attribute type: " ++ (show t) ++ " for " ++ s
                                                            
                                                            _ -> throwError $ "No such attribute: " ++ (show (head ids))

                                                    _ -> throwError $ "No such struct: " ++ ss

                                            Just t -> throwError $ "Not a struct type: " ++ (show t)   
                                                            
                                    _ -> throwError $ "No such struct instance: " ++ s    


        Change (Ident s) op e 
                            -> do
                                pos <- asks $ M.lookup s

                                case pos of
                                    Just (VDef p) -> do
                                        org <- gets $ M.lookup p

                                        case org of
                                            Just (MType Int) -> do
                                                val <- evalT e
                                                if val == MType Int
                                                    then runStmtT ret stmts
                                                    else throwError $ "Wrong type in change: " ++ (show val) ++ " for " ++ s

                                            Just t -> throwError $ "Wrong type to change: " ++ (show t) ++ " for " ++ s

                                    _ -> throwError $ "No such identifier in change: " ++ s


        ChangeAttr attr op e -> do
            te <- evalT e
            case te of
                MType Int -> runStmtT ret $ (IncrDecrA attr Incr) : stmts
                _ -> throwError $ "Not an int in change attribute: " ++ (show te)


        IncrDecr (Ident s) op 
                            -> do
                                pos <- asks $ M.lookup s
                                case pos of
                                    Just (VDef p) -> do
                                        org <- gets $ M.lookup p
                                        case org of
                                            Just (MType Int) -> runStmtT ret stmts

                                            Just t -> throwError $ "Wrong type in incr-/decrement: " ++ (show t) ++ " for " ++ s

                                    _ -> throwError $ "No such identifier in incr-/decrement: " ++ s                    


        IncrDecrA (Attrib (Ident s) (Ident at : ids)) op -> do
            jp <- asks $ M.lookup s

            case jp of 
                Just (VDef pos) -> do
                    jm <- gets $ M.lookup pos
    
                    case jm of
                        Just (MType (Struct (Ident ss))) -> do
                            jsd <- asks $ M.lookup ss
                            
                            case jsd of
                                Just (SDef m) ->
                                    
                                    case M.lookup at m of
                                        Just Int -> runStmtT ret stmts
                                        
                                        Just t -> throwError $ "Wrong attribute type: " ++ (show t) ++ " for " ++ s

                                        _ -> throwError $ "No such attribute: " ++ (show (head ids))

                                _ -> throwError $ "No such struct: " ++ ss

                        Just t -> throwError $ "Not a struct type: " ++ (show t)                        

                _ -> throwError $ "No such structure instance: " ++ s

        Ret e -> do
            val <- evalT e 
            if eq ret val
                then runStmtT val stmts
                else throwError $ "Wrong type in return: " ++ (show val) ++ " instead of " ++ (show ret)    

        VRet -> if eq ret (MType Void)
                then runStmtT (MType Void) stmts
                else throwError $ "Returned void instead of: " ++ (show ret)

        Cond e st -> do
            val <- evalT e
            case val of
                MType Bool -> do
                    env <- ask
                    val <- runStmtT ret [st]
                    let cont ret = local (\e -> env) $ runStmtT ret stmts
                    if eq ret val
                        then cont $ firstYet ret val
                        else throwError $ "Different return type in if cond: " ++ (show val) ++ " instead of " ++ (show ret)           

                _ -> throwError $ "Wrong type in if condition: " ++ (show val)


        CondElse e st1 st2 -> do
            val <- evalT e
            case val of
                MType Bool -> do
                    env <- ask
                    val1 <- runStmtT ret [st1]
                    val2 <- runStmtT ret [st2]
                    let cont ret = local (\e -> env) $ runStmtT ret stmts
                    if eq ret val1 && (eq ret val2)
                        then cont $ firstYet ret $ firstYet val1 val2
                        else throwError $ "Different return types in else if cond: " ++ (show val1) ++ " or " ++ (show val2) ++ " instead of " ++ (show ret)

                _ -> throwError $ "Wrong type in if/else condition: " ++ (show val)


        CondElif e st1 elifs st2 -> do
            case elifs of
                [] -> runStmtT ret $ (CondElse e st1 st2) : stmts
                ((Elf e st):elfs) -> do
                    val <- evalT e
                    env <- ask
                    case val of
                        MType Bool -> do
                            val <- runStmtT ret [st1]
                            let cont ret = local (\e -> env) $ runStmtT ret $ (CondElif e st elfs st2) : stmts
                            if eq ret val
                                then cont $ firstYet ret val
                                else throwError $ "Wrong type in elif return: " ++ (show val) ++ " instead of " ++ (show ret)

                        _ -> throwError $ "Wrong type in elif condition: " ++ (show val)


        While e st -> do
            val <- evalT e
            case val of
                MType Bool -> do
                    env <- ask
                    val <- runStmtT ret [st]
                    let cont ret = local (\e -> env) $ runStmtT ret stmts
                    let f val = if eq ret val
                        then cont $ firstYet ret val
                        else throwError $ "Wrong return type in while: " ++ (show val) ++ " instead of " ++ (show ret)
                    
                    case val of
                        MCont t -> f t
                        MBreak t -> f t
                        t -> f t

                _ -> throwError $ "Wrong type in while condition: " ++ (show val)

    
        InDecl (FunDef t (Ident s) par (Blck st)) ->
                    let
                        place [] = do
                            res <- runStmtT NotYet st
                            return res

                        place ((Param t (Ident x)):aN) = do

                            Just (Counter pos) <- gets $ M.lookup 0

                            modify $ M.insert pos $ MType t
                            modify $ M.insert 0 $ Counter $ pos + 1                            

                            let f = M.insert x $ VDef pos
                            
                            local f $ place aN
                    
                    in do
    
                        Just (Counter pos) <- gets $ M.lookup 0            

                        env <- ask

                        let env' = M.insert s (VDef pos) env
                        
                        modify $ M.insert pos $ MType $ Fun t $ getTypes par []
    
                        modify $ M.insert 0 $ Counter $ pos + 1
        
                        res <- local (\e -> env') $ place par

                        if (res == MType t) || (t == Void && res == NotYet) 
                            then local (\e -> env') $ runStmtT ret stmts
                            else throwError $ "Wrong return type: " ++ (show res) ++ " instead of " ++ (show t) ++ " in " ++ s


        Eval e -> do
            evalT e            
            runStmtT ret stmts

        Break -> do
            t <- runStmtT ret stmts
            case t of
                MBreak _ -> return t
                MCont _ -> return t
                _ -> return $ MBreak t
        

        Cont -> do
            t <- runStmtT ret stmts
            case t of
                MBreak _ -> return t
                MCont _ -> return t
                _ -> return $ MCont t


        Print e -> do
            evalT e
            runStmtT ret stmts


interpretT :: Prog -> ExceptT Exception (RWS Env Log ContextT) MType
interpretT (Program []) = return NotYet

interpretT (Program (def:defs)) = do
              
    case def of
        FnDecl (FunDef t (Ident s) args bl@(Blck st)) ->
            if s == "main" && (t /= Int)
                then throwError $ "Wrong type of main: " ++ (show t)
                else
                    let
                        place [] = do
                            res <- runStmtT NotYet st
                            return res

                        place ((Param t (Ident x)):aN) = do

                            Just (Counter pos) <- gets $ M.lookup 0

                            modify $ M.insert pos $ MType t
                            modify $ M.insert 0 $ Counter $ pos + 1                            

                            let f = M.insert x $ VDef pos
                            
                            local f $ place aN
                    
                    in do
    
                        Just (Counter pos) <- gets $ M.lookup 0            

                        env <- ask

                        let env' = M.insert s (VDef pos) env
                        
                        modify $ M.insert pos $ MType $ Fun t $ getTypes args []
    
                        modify $ M.insert 0 $ Counter $ pos + 1
        
                        res <- local (\e -> env') $ place args

                        if (res == MType t) || (t == Void && res == NotYet) 
                            then local (\e -> env') $ interpretT $ Program defs
                            else throwError $ "Wrong return type: " ++ (show res) ++ " instead of " ++ (show t) ++ " in " ++ s


        RecDef (Ident s) atr -> do
            let toMap [] = M.empty
                toMap ((AtrNotIn t (Ident s)):atrs) = M.insert s t $ toMap atrs
            let m = toMap atr
            let f = M.insert s $ SDef m
            local f $ interpretT $ Program defs

tryRun s = do
    let Ok p = pProg (myLexer s)
    let iniE = M.empty    
    let iniS = M.insert 0 (RInteger 1) M.empty
    let iniS' = M.insert 0 (Counter 1) M.empty
    let (r,s,w) = runRWS (runExceptT (interpretT p)) iniE iniS'
    case r of
        Left s -> hPutStrLn stderr $ "Error: " ++ s
        Right _ -> do
            let (r,s,w) = runRWS (runExceptT (interpret p)) iniE iniS
            let 
                output [] = putStrLn ""
                output (s:ss) = do
                    putStrLn s
                    output ss
            output w
            case r of
                Right i -> putStrLn $ show i
                Left s -> putStrLn $ "Error: " ++ s


main = do
    args <- getArgs
    case args of
        [] -> do
            contents <- getContents
            tryRun contents
        (arg:[]) -> withFile arg ReadMode (\handle -> do  
                contents <- hGetContents handle     
                tryRun contents) 

        _ -> putStrLn "Max. 1 argument"
