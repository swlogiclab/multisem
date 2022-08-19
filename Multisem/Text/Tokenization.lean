#print Char
#print String

class Tokenize (s:String) (G: outParam (List String)) where
  blah : Unit
class NonWS (c:Char) where
  blah : Unit

-- This will save a lot of typing String.mk
class cTokenize (s:List Char) (G: outParam (List String)) where
  blah : Unit
instance unpackString (l G)[cTokenize l G] : Tokenize (String.mk l) G where
  blah := ()
instance unpackString' (l G)[cTokenize l G] : Tokenize ({ data := l}) G where
  blah := ()

-- We go up to tokenization of 12-character words for now... because "non-negative" makes for some nice examples and it's 12 characters
-- A much nicer solution would be if we could use macros to just use String.splitOn at compile-time and then emit the resulting list term as the term, but this level of computation doesn't seem to be feasible right now.
-- We could probably overload a macro to tokenize statically up to a certain depth, but that's brittle and more painful to extend, plus this approach is still pretty quick in Coq (which has much slower TC resolution than Lean)

-- final word tokenization
instance tok1 (c)[NonWS c]: cTokenize ([c]) ([String.mk [c]]) where
  blah := ()
instance tok2 (c1 c2)[NonWS c1][NonWS c2]: cTokenize ([c1,c2]) ([String.mk [c1,c2]]) where
  blah := ()
instance tok3 (c1 c2 c3)[NonWS c1][NonWS c2][NonWS c3]: cTokenize ([c1,c2,c3]) ([String.mk [c1,c2,c3]]) where
  blah := ()
instance tok4 (c1 c2 c3 c4)[NonWS c1][NonWS c2][NonWS c3][NonWS c4]: cTokenize ([c1,c2,c3,c4]) ([String.mk [c1,c2,c3,c4]]) where
  blah := ()
instance tok5 (c1 c2 c3 c4 c5)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5]: cTokenize ([c1,c2,c3,c4,c5]) ([String.mk [c1,c2,c3,c4,c5]]) where
  blah := ()
instance tok6 (c1 c2 c3 c4 c5 c6)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6]: cTokenize ([c1,c2,c3,c4,c5,c6]) ([String.mk [c1,c2,c3,c4,c5,c6]]) where
  blah := ()
instance tok7 (c1 c2 c3 c4 c5 c6 c7)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7]: cTokenize ([c1,c2,c3,c4,c5,c6,c7]) ([String.mk [c1,c2,c3,c4,c5,c6,c7]]) where
  blah := ()
instance tok8 (c1 c2 c3 c4 c5 c6 c7 c8)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8]: cTokenize ([c1,c2,c3,c4,c5,c6,c7,c8]) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8]]) where
  blah := ()
instance tok9 (c1 c2 c3 c4 c5 c6 c7 c8 c9)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9]: cTokenize ([c1,c2,c3,c4,c5,c6,c7,c8,c9]) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9]]) where
  blah := ()
instance tok10 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10]: cTokenize ([c1,c2,c3,c4,c5,c6,c7,c8,c9,c10]) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10]]) where
  blah := ()
instance tok11 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10][NonWS c11]: cTokenize ([c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11]) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11]]) where
  blah := ()
instance tok12 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10][NonWS c11][NonWS c12]: cTokenize ([c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12]) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12]]) where
  blah := ()

instance tok1s (c:Char) (s:List Char) (l:List String)[NonWS c][cTokenize s l] : cTokenize (c::' '::s) ([(String.mk [c])]++l) where
  blah := ()
instance tok2s (c1 c2:Char) (s:List Char) (l:List String)[NonWS c1][NonWS c2][cTokenize s l] : cTokenize (c1::c2::' '::s) ([(String.mk [c1,c2])]++l) where
  blah := ()
instance tok3s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3)[NonWS c1][NonWS c2][NonWS c3]: cTokenize (c1::c2::c3::' '::s) ([String.mk [c1,c2,c3]]++l) where
  blah := ()
instance tok4s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4)[NonWS c1][NonWS c2][NonWS c3][NonWS c4]: cTokenize (c1::c2::c3::c4::' '::s) ([String.mk [c1,c2,c3,c4]]++l) where
  blah := ()
instance tok5s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5]: cTokenize (c1::c2::c3::c4::c5::' '::s) ([String.mk [c1,c2,c3,c4,c5]]++l) where
  blah := ()
instance tok6s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6]: cTokenize (c1::c2::c3::c4::c5::c6::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6]]++l) where
  blah := ()
instance tok7s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7]: cTokenize (c1::c2::c3::c4::c5::c6::c7::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7]]++l) where
  blah := ()
instance tok8s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7 c8)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8]: cTokenize (c1::c2::c3::c4::c5::c6::c7::c8::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8]]++l) where
  blah := ()
instance tok9s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7 c8 c9)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9]: cTokenize (c1::c2::c3::c4::c5::c6::c7::c8::c9::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9]]++l) where
  blah := ()
instance tok10s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10]: cTokenize (c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10]]++l) where
  blah := ()
instance tok11s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10][NonWS c11]: cTokenize (c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11]]++l) where
  blah := ()
instance tok12s (s:List Char)(l:List String)[cTokenize s l] (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12)[NonWS c1][NonWS c2][NonWS c3][NonWS c4][NonWS c5][NonWS c6][NonWS c7][NonWS c8][NonWS c9][NonWS c10][NonWS c11][NonWS c12]: cTokenize (c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::' '::s) ([String.mk [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12]]++l) where
  blah := ()


-- Doing this in Coq is much less painful, since characters there are represented as 8-vectors of bits, so this can be done for anything with a bit disinguishing from whitespace (and that generalizes to unicode)
-- Hopefully the large number of instances here won't cause an issue once we include capitals and non-ASCII characters
instance nws_a : NonWS 'a' where 
  blah := ()
instance nws_a' : NonWS (Char.ofNat 97) where 
  blah := ()
instance nws_b : NonWS 'b' where 
  blah := ()
instance nws_c : NonWS 'c' where 
  blah := ()
instance nws_d : NonWS 'd' where 
  blah := ()
instance nws_e : NonWS 'e' where 
  blah := ()
instance nws_f : NonWS 'f' where 
  blah := ()
instance nws_g : NonWS 'g' where 
  blah := ()
instance nws_h : NonWS 'h' where 
  blah := ()
instance nws_i : NonWS 'i' where 
  blah := ()
instance nws_j : NonWS 'j' where 
  blah := ()
instance nws_k : NonWS 'k' where 
  blah := ()
instance nws_l : NonWS 'l' where 
  blah := ()
instance nws_m : NonWS 'm' where 
  blah := ()
instance nws_n : NonWS 'n' where 
  blah := ()
instance nws_o : NonWS 'o' where 
  blah := ()
instance nws_p : NonWS 'p' where 
  blah := ()
instance nws_q : NonWS 'q' where 
  blah := ()
instance nws_r : NonWS 'r' where 
  blah := ()
instance nws_s : NonWS 's' where 
  blah := ()
instance nws_t : NonWS 't' where 
  blah := ()
instance nws_u : NonWS 'u' where 
  blah := ()
instance nws_v : NonWS 'v' where 
  blah := ()
instance nws_w : NonWS 'w' where 
  blah := ()
instance nws_x : NonWS 'x' where 
  blah := ()
instance nws_y : NonWS 'y' where 
  blah := ()
instance nws_z : NonWS 'z' where 
  blah := ()
instance nws_0 : NonWS '0' where 
  blah := ()
instance nws_1 : NonWS '1' where 
  blah := ()
instance nws_2 : NonWS '2' where 
  blah := ()
instance nws_3 : NonWS '3' where 
  blah := ()
instance nws_4 : NonWS '4' where 
  blah := ()
instance nws_5 : NonWS '5' where 
  blah := ()
instance nws_6 : NonWS '6' where 
  blah := ()
instance nws_7 : NonWS '7' where 
  blah := ()
instance nws_8 : NonWS '8' where 
  blah := ()
instance nws_9 : NonWS '9' where 
  blah := ()
instance nws_dash : NonWS '-' where 
  blah := ()

-- Debugging tool for checking instance resolution
def reqNonWS (c:Char)[NonWS c] : UInt32 :=
  match c with
  | Char.mk n _ => n

@[simp]
def assertTokenization (s:String) (l:List String) [Tokenize s l] : Prop := True
@[simp]
def assertCTokenization (s:List Char) (l:List String) [cTokenize s l] : Prop := True

def manual0 : cTokenize ['a'] ["a"] := tok1 _ 
def manual0' : cTokenize [Char.ofNat 97] ["a"] := tok1 _ 
def manual1 : cTokenize ['a','b'] ["ab"] := tok2 'a' 'b'
#print Char.ofNat
def ex0 := assertCTokenization ['a'] ["a"]
def ex1_0 := assertTokenization (String.mk ['a']) (["a"])
def ex1_1 := assertTokenization ({ data := ['a']}) (["a"])
-- Unification problems
--def ex1 := assertTokenization "a" (["a"])
def checkStrAssumption : String.mk ['a'] = "a" :=
  by rfl

-- Unification problems
--def ex1 := assertTokenization "one is one" (["one"]++(["is"]++["one"]))
--def ex2 := assertTokenization "a b c d" (["a"]++(["b"]++(["c"]++["d"])))
--def ex2 := assertTokenization "every natural is odd or even" (["every"] ++ (["natural"] ++ (["is"] ++ (["odd"] ++ (["or"] ++ ["even"])))))


#print UInt32.isValidChar
#print Nat.isValidChar
theorem sp_is_valid : UInt32.isValidChar 32 :=
  by simp

#eval (Char.mk 32 sp_is_valid)

