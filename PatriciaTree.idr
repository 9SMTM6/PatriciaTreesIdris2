import Data.List
import Data.Vect
import Decidable.Equality

Key : (len: Nat) -> Type
Key len = Vect len Bool

data PatricaTree : (len : Nat) -> tVal -> Type where
    -- Empty : PatricaTree 0 tVal
    Leaf : 
        {finLen : Nat} -> 
        Key finLen -> (val: tVal) -> PatricaTree finLen tVal
    Node :
        -- I need these accessible in some methods (or at least its helpful and how I got to solutions the type checker accepts)
        -- (or I implement and use a selfmade function to recalculate the lenght and generate a dependent pair, but this is quicker)
        -- order matters for these!
        -- if prefixLen comes after usage,
        -- compiler accepts it, but latter one gets weird
        -- 'is not accessible' errors.
        -- seems its perfectly happy shadowing these...
        -- seems like a bug?
        {prefixLen: Nat} ->
        {suffixLen: Nat} ->
        Key prefixLen -> 
        (left : PatricaTree suffixLen tVal) -> 
        (right : PatricaTree suffixLen tVal) ->
        PatricaTree (S (prefixLen + suffixLen)) tVal

total
implementation
Show tVal => Show (PatricaTree len tVal) where
    show trie = ?show
    -- show trie = hlp_showNested 0 trie
    -- show Empty = "[ ]"
    -- show (Leaf x) = "[" ++ show x ++ "]"
    -- show (Node xs left right) = " o \n |\\\n | \\\n |  \\\n" ++ " |   \\\n" ++ (show left) ++ " " ++ (show right)

total
singleton : {1 len: Nat} -> Key len -> tVal -> PatricaTree len tVal
singleton [] val = Leaf [] val
-- and finally I understand rewrite rules. Somewhat. I have no idea how to use them in do blocks
-- singleton (False :: postfix) val = rewrite sym (plusZeroRightNeutral len) in (Node postfix (Leaf [] val) Empty)
-- singleton (True  :: postfix) val = rewrite sym (plusZeroRightNeutral len) in (Node postfix Empty (Leaf [] val))
singleton _ _ = ?sing

total
%hint
hlp_compareNat : (len: Nat) -> (compareNat len len) = EQ
hlp_compareNat 0 = Refl
hlp_compareNat (S k) = hlp_compareNat k

total
%hint
hlp_eqNotLt : (len: Nat) -> (compareNat len len) = LT -> Void
hlp_eqNotLt 0 Refl impossible
-- hlp_eqNotLt (S k) (cong Refl) impossible
-- hlp_eqNotLt (S k) cmp = rewrite (sym (cong ?hlp cmp)) in (hlp_eqNotLt k)
-- hlp_eqNotLt (S k) cmp = ?neq (hlp_eqNotLt k)
hlp_eqNotLt (S k) cmp with (cmp = (compareNat k k = LT))
    _ | res = do
        let wedv = ?eq_in (hlp_eqNotLt k)
        ?eq
    
    -- rewrite (sym cmp) in (hlp_eqNotLt k)

hlp_ifReduction : {len: Nat} -> (if (compareNat len len) == LT then len else len) = len
hlp_ifReduction = ?red

total
-- theres probably more efficient ways to do that, but here we go
hlp_findCommonPrefixLen : {len1: Nat} -> {len2: Nat} -> Key len1 -> Key len2 -> Fin (S (min len1 len2))
hlp_findCommonPrefixLen [] _ = 0
hlp_findCommonPrefixLen _ [] = 0
hlp_findCommonPrefixLen (x :: xs) (y :: ys) =
    case x == y of
        True => ?what (FS (hlp_findCommonPrefixLen xs ys))
        False => 0

-- total
-- hlp_findCommonPrefix : {len1: Nat} -> {len2: Nat} -> {len3: Fin (min len1 len2) } -> Key len1 -> Key len2 -> Key (cast len3)

total
insert : {len: Nat} -> Key len -> tVal -> PatricaTree len tVal -> PatricaTree len tVal
-- insert [] val Empty = Leaf [] val
insert [] val (Leaf [] _) = ?ins_0
-- Leaf [] val
insert (False :: xs) val (Node ys left right) = ?ins_4
insert (True :: xs) val (Node ys left right) = ?ins_5
insert (False :: _) _ (Leaf _ _) = ?ins_7
insert (True :: _) _ (Leaf _ _) = ?ins_8
-- insert [] val _ = Leaf val
-- -- if held key has len 0, the node was in the split location already, so we recurse into the correct location
-- insert (False :: xs) val (Node [] left right) = Node [] (insert xs val left) right
-- insert (True :: xs) val (Node [] left right) = Node [] left (insert xs val right)
-- -- otherwise we need to search for the location they split
-- insert (False :: xs) val (Node {prefixLen = pL} ys left right) = do
--     let (nodeLenInsertKeyPt, rem) = splitAt pL xs
--     let nodeMatchesIns = isPrefixOf nodeLenInsertKeyPt ys
--     let newLeft = (if nodeMatchesIns
--             then ?ins_0
--             else ?ins_1
--             )
--     -- should be doable now that I can access prefixlen etc
--     -- let splitIdx = hlp_findCommonPrefixLen xs ys
--     -- let commonPrefix = splitAt splitIdx xs
--     let laa = 4
--     -- let laaaa = zip xs ys
    
--     -- using:
--     -- span
    
--     -- let cmp = zip (take (length ys) xs) ys
--     let lee =
--         case ys of 
--             [] => ?ins_inner
--             -- (Node [] (insert xs val left) right)
--             (x :: zs) => ?ins_inner_1
--     -- let laa = case ys of
--     --         [] => ?ins_emb3
--     --         [z::zs] => ?ins_emb2
--     ?ins
-- -- doesn't work: ys doesnt have to have len 0
-- -- ?what3 (Node ys (insert xs val left) right)
-- insert (True :: xs) val (Node ys left right) = ?ins_6

actualLen : (arg: PatricaTree len tVal) -> Nat

total
lookup : Key len -> PatricaTree len tVal -> Maybe tVal
-- lookup [] Empty = Nothing
lookup [] (Leaf [] x) = Just x
-- lookup (False :: xs) Empty = Nothing
-- lookup (True :: xs) Empty = Nothing
lookup (False :: xs) (Node {prefixLen = pL} ys left _) = do
    let (nodeLenLookupKeyPt, rem) = splitAt pL xs
    let nodeMatchesLookup = isPrefixOf nodeLenLookupKeyPt ys
    if nodeMatchesLookup
        then lookup rem left
        else Nothing
lookup (True :: xs) (Node {prefixLen = pL} ys _ right) = do
    let (nodeLenLookupKeyPt, rem) = splitAt pL xs
    let nodeMatchesLookup = isPrefixOf nodeLenLookupKeyPt ys
    if nodeMatchesLookup
        then lookup rem right
        else Nothing
lookup (False :: _) (Leaf _ _) = ?lkp_1
lookup (True :: _) (Leaf _ _) = ?lkp_2

total
intersection : {len:Nat} -> PatricaTree len tVal -> PatricaTree len tVal -> PatricaTree len tVal
-- intersection Empty _ = Empty
-- intersection _ Empty = Empty
intersection (Leaf _ x) winner@(Leaf _ y) = ?int_0
-- winner
intersection (Leaf _ _) (Node _ _ _) = ?int_1
intersection (Node _ _ _) (Leaf _ _) = ?int_2
-- this does not get accepted due to inability to solve contraint...
-- it seems to want to patch prefixLen between both Nodes?
-- But without these cases its not complete...
-- intersection (Node _ _ _) (Node _ _ _) = ?int_3
-- this does... But I'm not sure its really doing the right thing?
intersection (Node {prefixLen = 0} _ _ _) (Node _ _ _) = ?int_4
intersection (Node {prefixLen = 1, suffixLen = 1} _ _ _) (Node {prefixLen = 1, suffixLen = 1} _ _ _) = ?int_5

total
union : PatricaTree len tVal -> PatricaTree len tVal -> PatricaTree len tVal
-- union Empty only = only
-- union only Empty = only
union (Leaf _ x) winner@(Leaf _ y) = ?un_2
-- winner
-- this does not sit right with me...
-- theres either case missing or something else I'm overlooking
-- but it tests as total...
-- union only@(Node xs left right) Empty = only
union (Leaf _ _) (Node _ _ _) = ?un_0
union (Node _ _ _) (Leaf _ _) = ?un_1

total
delete: Key len -> PatricaTree len tVal -> PatricaTree len tVal
-- delete [] Empty = Empty
-- delete [] (Leaf _ x) = Empty
-- delete (x :: xs) Empty = Empty
delete (False :: xs) (Node {prefixLen = pL} ys left right) = Node ys (delete (drop pL xs) left) right
delete (True :: xs) (Node {prefixLen = pL} ys left right) = Node ys left (delete (drop pL xs) right)
delete (False :: _) (Leaf _ _) = ?del_0
delete (True :: _) (Leaf _ _) = ?del_1
delete _ _ = ?del

exKey: Key 4
exKey = [True, False, True, True]
ex = singleton exKey 6
exLkp = lookup exKey ex
exDel = delete exKey ex
exKey2: Key 4
exKey2 = [True, False, False, False]
ex2 = singleton exKey2 5
exUnion = union ex ex2
ex3: PatricaTree 5 Nat
ex3 = Node ([False, True]) (Node ([False]) (Leaf [] 5) (Leaf [] 4)) (Node ([False]) (Leaf [] 6) (Leaf [] 1))
ex4: PatricaTree 6 Nat
ex4 = Node ([False, True]) (Node ([False]) (Node [] (Leaf [] 5) (Leaf [] 3)) (Node [] (Leaf [] 4) (Leaf [] 1))) (Node ([False, True]) (Leaf [] 6) (Leaf [] 1))
-- exIns = insert

-- main : IO ()
-- main = do
-- the show impl I had was absolutely hacky,
-- trying to show things top down, which is difficult.
-- it was created when I was already tired from
-- trying to debug something else.
--     -- printLn ex
--     -- printLn ex2
--     -- printLn exUnion
--     -- printLn ex3
--     -- printLn ex4
--     pure ()
