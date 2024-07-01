import Data.List (intersperse)
import Data.Map (Map)
import Data.Set (Set)
import Numeric.Natural (Natural)
import System.Exit (ExitCode(ExitFailure), exitWith)
import System.IO (hPutStrLn, stderr)
import qualified Data.Map as Map
import qualified Data.Set as Set

class Label t where
    label :: t -> [Char]

instance Label Char where
    label c = [c]

instance Label Int where
    label i = show i

data Re t =
      Void
    | Epsilon
    | Symbol t
    | Union (Re t) (Re t)
    | Concat (Re t) (Re t)
    | Repeat (Re t)
    deriving Show

data Nfa t = MkNfa { 
    nstates :: Natural,
    nfinal0 :: Natural,
    ndeltas :: [(Natural, Maybe t, Natural)]
}
    deriving Show

data Dfa t = MkDfa {
    dstates :: Natural,
    dsymbols :: [t],
    dfinals :: Set Natural,
    ddeltas :: Map Natural (Map t Natural)
}
    deriving Show

repeatAtLeast :: Natural -> Re t -> Re t
repeatAtLeast 0 re = Union Epsilon $ Repeat re
repeatAtLeast 1 re = Repeat re
repeatAtLeast lo re = Concat re $ repeatAtLeast (lo-1) re

repeatRange :: Natural -> Natural -> Re t -> Re t
repeatRange 0 0 re = Epsilon
repeatRange 0 1 re = Union Epsilon re
repeatRange 0 hi re = Union Epsilon $ Concat re $ repeatRange 0 (hi-1) re
repeatRange 1 1 re = re
repeatRange lo hi re = Concat re $ repeatRange (lo-1) (hi-1) re

reParse :: [Char] -> Maybe (Re Char)
reParse str | (re, "") <- expr str = Just re
  where
    isSym c = ('a' <= c && c <= 'z' ||
               'A' <= c && c <= 'Z')
    digit c =
        if '0' <= c && c <= '9' then Just $ (read::String->Natural) [c]
        else Nothing
    atom (c:s) | isSym c = Just (Symbol c, s)
    atom ('(':s) | (re, ')':s') <- expr s = Just (re, s')
    atom ('[':']':s) = Just (Void, s)
    atom ('[':s) = loop s
      where
        loop (c:']':s) | isSym c = Just (Symbol c, s)
        loop (c:s) | isSym c, Just (re, s') <- loop s =
            Just (Union (Symbol c) re, s')
        loop _ = Nothing
    atom _ = Nothing
    mod ('?':s) = (Union Epsilon, s)
    mod ('+':s) = (Repeat, s)
    mod ('*':s) = (Union Epsilon . Repeat, s)
    mod (s@('{':'}':_)) = (id, s)
    mod ('{':s) | Just (f, s') <- loop1 s 0 = (f, s')
      where
        loop1 (c:s) i | Just d <- digit c = loop1 s $ 10*i+d
        loop1 (',':'}':s) i = Just (repeatAtLeast i, s)
        loop1 (',':s) i = loop2 s i 0
        loop1 ('}':s) i = Just (repeatRange i i, s)
        loop1 _ _ = Nothing
        loop2 (c:s) i j | Just d <- digit c = loop2 s i $ 10*j+d
        loop2 ('}':s) i j | i <= j = Just (repeatRange i j, s)
        loop2 _ _ _ = Nothing
    mod s = (id, s)
    atomMod s | Just (re, s') <- atom s, (f, s'') <- mod s' = Just (f re, s'')
    atomMod s = Nothing
    term s | Just (re, s') <- atomMod s = loop s' re id
      where
        loop s re0 cc | Just (re, s') <- atomMod s =
            loop s' re $ cc . Concat re0
        loop s re0 cc = (cc re0, s)
    term s = (Epsilon, s)
    expr s =
        case term s of
        (re, '|':s') | (re', s'') <- expr s'
           -> (Union re re', s'')
        (re, s') -> (re, s')
reParse _ = Nothing

nfaFromRe :: Re t -> Nfa t
nfaFromRe Void = MkNfa { nstates = 1, nfinal0 = 1, ndeltas = [] }
nfaFromRe Epsilon = MkNfa { nstates = 1, nfinal0 = 0, ndeltas = [] }
nfaFromRe (Symbol e) = MkNfa { nstates = 2, nfinal0 = 1, ndeltas = [(0, Just e, 1)] }
nfaFromRe (Union re1 re2) =
    MkNfa { 
        nstates = 1 + nstates nfa1 + nstates nfa2,
        nfinal0 = 1 + nfinal0 nfa1 + nfinal0 nfa2,
        ndeltas = (0, Nothing, inject1 0):(0, Nothing, inject2 0):
            ((\(u, e, v) -> (inject1 u, e, inject1 v)) <$> ndeltas nfa1) ++
            ((\(u, e, v) -> (inject2 u, e, inject2 v)) <$> ndeltas nfa2)
    }
  where
    nfa1 = nfaFromRe re1
    nfa2 = nfaFromRe re2
    inject1 v =
        if v >= nfinal0 nfa1 then 1 + nfinal0 nfa2 + v
        else 1 + v
    inject2 v =
        if v >= nfinal0 nfa2 then 1 + nstates nfa1 + v
        else 1 + nfinal0 nfa1 + v
nfaFromRe (Concat re1 re2) =
    MkNfa {
        nstates = nstates nfa1 + nstates nfa2,
        nfinal0 = nstates nfa1 + nfinal0 nfa2,
        ndeltas = ndeltas nfa1 ++
            ((\v -> (v, Nothing, nstates nfa1)) <$> [nfinal0 nfa1..nstates nfa1 - 1]) ++
            ((\(u, e, v) -> (nstates nfa1 + u, e, nstates nfa1 + v)) <$> ndeltas nfa2)
    }
  where
    nfa1 = nfaFromRe re1
    nfa2 = nfaFromRe re2
nfaFromRe (Repeat re) =
    MkNfa {
        nstates = nstates nfa,
        nfinal0 = nfinal0 nfa,
        ndeltas = ndeltas nfa ++
            ((\v -> (v, Nothing, 0)) <$> [nfinal0 nfa..nstates nfa - 1])
    }
  where
    nfa = nfaFromRe re

graphvizNfa :: Label t => Nfa t -> String
graphvizNfa nfa =
    "digraph {\n  node [shape=circle];\n " ++
    concat (((" " ++) . show) <$> [0..nfinal0 nfa - 1]) ++
    "\n  node [shape=doublecircle];\n " ++
    concat (((" " ++) . show) <$> [nfinal0 nfa..nstates nfa - 1]) ++
    "\n" ++ concat (showEdge <$> Map.toList edges) ++ "}"
  where
    showEdge ((u, v), es) =
        "  " ++ show u ++ " -> " ++ show v ++ " [label=\"" ++ concat (intersperse "," (map lbl es)) ++ "\"];\n"
    edges = foldr (\(u, e, v) m -> Map.insertWith (++) (u,v) [e] m) Map.empty (ndeltas nfa)
    lbl (Just e) = label e
    lbl Nothing = "\"ε\""

dfaFromNfa nfa =
    let q0 = closure (Set.fromList [0]) in
    let (dton, states, deltas) = genStates (Map.singleton 0 q0, Map.singleton q0 0, 1, Map.empty) 0 in
    let finals = finalize states dton in
    MkDfa {
        dstates = states,
        dsymbols = symbols,
        dfinals = finals,
        ddeltas = deltas
    }
  where
    symbols = [ e | (_, Just e, _) <- ndeltas nfa ]
    trans = foldr 
        (\(u, e, v) m ->
            Map.insertWith Set.union (u, e) (Set.singleton v) m
        ) Map.empty (ndeltas nfa)
    move e qs = Set.unions
        (Set.map (\q -> Map.findWithDefault Set.empty (q, e) trans) qs)
    closure qs | qs' <- move Nothing qs =
        if qs' `Set.isSubsetOf` qs then qs
        else closure (Set.union qs' qs)
    genStates (dton, ntod, states, deltas) q =
        if q == states then (dton, states, deltas)
        else let (dton', ntod', states', qd) = 
                  foldr (update q) (dton, ntod, states, Map.empty) symbols in
        genStates (dton', ntod', states', Map.insert q qd deltas) (q + 1)
    update q e (dton, ntod, states, deltas) =
        let adj = closure $ move (Just e) $ (Map.!) dton q in
        case Map.lookup adj ntod of
        Just i -> (dton, ntod, states, Map.insert e i deltas)
        Nothing -> (Map.insert states adj dton,
                    Map.insert adj states ntod,
                    states + 1,
                    Map.insert e states deltas)
    finalize states dton =
        let isfinal s = Set.foldr (\v b -> b || v >= nfinal0 nfa) False s in
        Map.keysSet $ Map.filter isfinal dton

minimizeDfa dfa =
    MkDfa {
        dstates = fromIntegral (Set.size stateMap1Values),
        dsymbols = dsymbols dfa,
        dfinals = Set.map ((Map.!) stateMap2) (dfinals dfa),
        ddeltas = Map.map (Map.mapMaybe (\v -> Map.lookup v stateMap2)) $
            Map.mapKeys ((Map.!) stateMap2) $
            Map.filterWithKey (\u _ -> (Map.!) stateMap1 u == u && Map.member u stateMap2) $ ddeltas dfa
    }
  where
    {- (x,y) in cls if x and y can be merged -}
    cls0 = 
        Set.fromList [ 
            (u, v) | u <- [0..dstates dfa - 1], v <- [0..dstates dfa - 1],
            Set.member u (dfinals dfa) == Set.member v (dfinals dfa)
        ]
    clsupdate cls =
        let cls' = Set.filter (\(u, v) -> all (check cls u v) (dsymbols dfa)) cls in
        if cls' == cls then cls else clsupdate cls'
    check cls u v sym =
        Set.member ((Map.!) ((Map.!) (ddeltas dfa) u) sym, (Map.!) ((Map.!) (ddeltas dfa) v) sym) cls
    cls = clsupdate cls0
    isTrash u = all (\sym -> (Map.!) ((Map.!) (ddeltas dfa) u) sym == u) (dsymbols dfa)
    stateMap1 = Set.foldr (\(u, v) m -> Map.insertWith min u v m) Map.empty cls
    stateMap1Values = Set.filter (not . isTrash) $ Set.fromList $ Map.elems stateMap1
    stateMap2 = Map.mapMaybe (\v -> fromIntegral <$> Set.lookupIndex v stateMap1Values) stateMap1

nfaFromDfa :: Dfa t -> Nfa t
nfaFromDfa dfa =
    MkNfa {
        nstates = dstates dfa,
        nfinal0 = final0,
        ndeltas = deltas
    }
  where
    stateMap u =
        case Set.lookupLE u $ dfinals dfa of
            Just v | u == v -> final0 + fromIntegral (Set.findIndex v (dfinals dfa))
            Just v -> u - fromIntegral (Set.findIndex v (dfinals dfa)) - 1
            Nothing -> u
    final0 = dstates dfa - fromIntegral (Set.size (dfinals dfa))
    deltas = Map.foldrWithKey (\u m l -> Map.foldrWithKey (\e v l' -> (stateMap u, Just e, stateMap v):l') l m) [] $ ddeltas dfa

main :: IO ()
main = do
    s <- getLine
    case reParse s of
        Just r -> do
            putStrLn $ graphvizNfa $ nfaFromDfa $ minimizeDfa $ dfaFromNfa $ nfaFromRe r
        Nothing -> do
            hPutStrLn stderr "parse error"
            exitWith (ExitFailure 1)
