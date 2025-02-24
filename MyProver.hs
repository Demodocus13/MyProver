{-# LANGUAGE LambdaCase #-}
import Data.Char (isSpace)
import Control.Monad (when)

-- 命题的数据
data Prop
    = Var String        
    | Implies Prop Prop
    | Not Prop         
    | And Prop Prop    
    | Or Prop Prop     
    | Bottom           
    deriving (Eq, Show)

-- 推理规则的数据
data Proof
    = Assumption Prop                            
    | ImpliesIntro Prop Proof                   
    | ImpliesElim Proof Proof                                              
    | FalsumIntro Proof                          
    | ProofError String                         
    deriving (Show)

tokenize :: String -> [String]
tokenize [] = []
tokenize (c:cs)
    | c `elem` "→∧∨¬()" = [c] : tokenize cs  
    | isSpace c = tokenize cs                
    | otherwise = let (var, rest) = span (\x -> not (isSpace x) && not (x `elem` "→∧∨¬()")) (c:cs)
                 in var : tokenize rest      


-- 解析命题
parse :: String -> Maybe Prop
parse input = case parseImplies (tokenize input) of
    Just (prop, []) -> Just (convert prop)  -- 转换后返回结果
    _ -> Nothing


-- 解析to的部分
parseImplies :: [String] -> Maybe (Prop, [String])
parseImplies tokens = case parseOr tokens of
    Just (left, rest) -> parseImpliesRest left rest
    Nothing -> Nothing

parseImpliesRest :: Prop -> [String] -> Maybe (Prop, [String])
parseImpliesRest left ("→" : rest) = case parseOr rest of
    Just (right, rest') -> parseImpliesRest (Implies left right) rest'
    Nothing -> Just (left, rest)
parseImpliesRest left rest = Just (left, rest)

-- 解析lor的部分
parseOr :: [String] -> Maybe (Prop, [String])
parseOr tokens = case parseAnd tokens of
    Just (left, rest) -> parseOrRest left rest
    Nothing -> Nothing

parseOrRest :: Prop -> [String] -> Maybe (Prop, [String])
parseOrRest left ("∨" : rest) = case parseAnd rest of
    Just (right, rest') -> parseOrRest (Or left right) rest'
    Nothing -> Just (left, rest)
parseOrRest left rest = Just (left, rest)

-- 解析land的部分
parseAnd :: [String] -> Maybe (Prop, [String])
parseAnd tokens = case parseNot tokens of
    Just (left, rest) -> parseAndRest left rest
    Nothing -> Nothing

parseAndRest :: Prop -> [String] -> Maybe (Prop, [String])
parseAndRest left ("∧" : rest) = case parseNot rest of
    Just (right, rest') -> parseAndRest (And left right) rest'
    Nothing -> Just (left, rest)
parseAndRest left rest = Just (left, rest)

-- 解析neg的部分
parseNot :: [String] -> Maybe (Prop, [String])
parseNot ("¬" : rest) = case parseAtom rest of
    Just (prop, rest') -> Just (Not prop, rest')
    Nothing -> Nothing
parseNot tokens = parseAtom tokens

-- 解析原子命题
parseAtom :: [String] -> Maybe (Prop, [String])
parseAtom (var:rest) 
    | var `elem` ["A","B", "C", "D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"] = Just (Var var, rest)
parseAtom ("(" : rest) = case parseImplies rest of
    Just (prop, (")":rest')) -> Just (prop, rest')
    _ -> Nothing
parseAtom _ = Nothing

-- 转换\to,\bottom范式
convert :: Prop -> Prop
convert (And p q)         = Implies (convert (Not p)) (convert (Not q))  
convert (Or p q)          = Implies (convert (Not p)) (convert q)        
convert (Not (Not p))     = convert p                                   
convert (Not p)           = Implies (convert p) Bottom                 
convert (Implies p q)     = Implies (convert p) (convert q)        
convert p                 = p      

-- -- 转换为析取范式（DNF）
-- convertDNF :: Prop -> Prop
-- convertDNF (And p q)         = And (convertDNF p) (convertDNF q)  
-- convertDNF (Or p q)          = Or (convertDNF p) (convertDNF q)   
-- convertDNF (Not (Not p))     = convertDNF p   
-- convertDNF (Not p)           = Not (convertDNF p)               
-- convertDNF (Implies p q)     = Or (convertDNF (Not p)) (convertDNF q)
-- convertDNF (Iff p q)         = Or (And (convertDNF p) (convertDNF q)) (And (convertDNF (Not p)) (convertDNF (Not q)))
-- convertDNF p                 = p

-- -- 转换为合取范式（CNF）
-- convertCNF :: Prop -> Prop
-- convertCNF (And p q)         = And (convertCNF p) (convertCNF q)  
-- convertCNF (Or p q)          = Or (convertCNF p) (convertCNF q)   
-- convertCNF (Not (Not p))     = convertCNF p   
-- convertCNF (Not p)           = Not (convertCNF p)               
-- convertCNF (Implies p q)     = Or (convertCNF (Not p)) (convertCNF q)
-- convertCNF (Iff p q)         = And (Or (convertCNF p) (convertCNF q)) (Or (convertCNF (Not p)) (convertCNF (Not q)))
-- convertCNF p                 = p


data ProofState = ProofState { context :: [(String, Prop)], goal :: Prop }

--证明命题
prove :: ProofState -> (Either Proof String, [String])  
prove state = case goal state of
    Implies p q -> let (success1, steps1) = prove (state { goal = p })
                       (success2, steps2) = prove (state { goal = q })
                   in (combineProof success1 success2 ImpliesElim, steps1 ++ steps2)
    Bottom -> (Left (FalsumIntro (Assumption Bottom)), ["矛盾命题无法推导"])
    Var var -> (Left (Assumption (Var var)), [var ++ " 已知命题，可以推导"])
    _ -> (Right "无法证明该命题", ["无法证明该命题"])

combineProof :: Either Proof String -> Either Proof String -> (Proof -> Proof -> Proof) -> Either Proof String
combineProof (Left p1) (Left p2) rule = Left (rule p1 p2)
combineProof (Right err) _ _ = Right err
combineProof _ (Right err) _ = Right err

proveImpliesElim :: Proof -> Proof -> Either Proof String
proveImpliesElim (ImpliesIntro p proof) (Assumption p1) = 
    combineProof (Left proof) (Left (Assumption p1)) ImpliesElim
proveImpliesElim _ _ = Right "推理错误"

main :: IO ()
main = do
    putStrLn "欢迎！"
    proofLoop
    putStrLn "886"

proofLoop :: IO ()
proofLoop = do
    putStrLn "\n请输入命题逻辑语句（或输入“退出”以结束）："
    input <- getLine
    when (input /= "退出") $ do
        case parse input of
            Just parsedProp -> do
                putStrLn $ "解析成功: " ++ show parsedProp
                let initialState = ProofState { context = [("P", Var "P"), ("Q", Var "Q")], goal = parsedProp }
                let (result, steps) = prove initialState
                case result of
                    Left proof -> do
                        putStrLn "命题可证明。"
                        putStrLn "证明过程："
                        print proof
                    Right err -> putStrLn err
            Nothing -> putStrLn "解析失败，格式错误。"
        proofLoop  