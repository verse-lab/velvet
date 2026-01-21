import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def extractWords (s : String) : List String :=
  (s.split (· = ' ')).filter (· ≠ "")


def noLeadingSpaces (s : String) : Bool :=
  s.data.head? ≠ some ' '


def noTrailingSpaces (s : String) : Bool :=
  s.data.getLast? ≠ some ' '


def noConsecutiveSpaces (s : String) : Bool :=
  let chars := s.data
  chars.length < 2 ∨ (List.zip chars chars.tail).all (fun (a, b) => ¬(a = ' ' ∧ b = ' '))


def isProperlyFormatted (s : String) : Bool :=
  s = "" ∨ (noLeadingSpaces s ∧ noTrailingSpaces s ∧ noConsecutiveSpaces s)




def ensures1 (words_str : String) (result : String) : Prop :=
  extractWords result = (extractWords words_str).reverse


def ensures2 (words_str : String) (result : String) : Prop :=
  isProperlyFormatted result

def precondition (words_str : String) : Prop :=
  True

def postcondition (words_str : String) (result : String) : Prop :=
  ensures1 words_str result ∧
  ensures2 words_str result


def test1_words_str : String := "the sky is blue"

def test1_Expected : String := "blue is sky the"

def test2_words_str : String := "  hello world  "

def test2_Expected : String := "world hello"

def test3_words_str : String := "a good   example"

def test3_Expected : String := "example good a"







section Proof
theorem test1_precondition :
  precondition test1_words_str := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_words_str test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_words_str test1_Expected
  unfold extractWords isProperlyFormatted noLeadingSpaces noTrailingSpaces noConsecutiveSpaces
  native_decide

theorem test2_precondition :
  precondition test2_words_str := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_words_str test2_Expected := by
  unfold postcondition ensures1 ensures2
  unfold test2_words_str test2_Expected
  unfold extractWords isProperlyFormatted noLeadingSpaces noTrailingSpaces noConsecutiveSpaces
  native_decide

theorem test3_precondition :
  precondition test3_words_str := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_words_str test3_Expected := by
  unfold postcondition ensures1 ensures2 test3_words_str test3_Expected
  unfold extractWords isProperlyFormatted noLeadingSpaces noTrailingSpaces noConsecutiveSpaces
  native_decide

theorem uniqueness_0
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    : ensures1 words_str ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    : ensures1 words_str ret2 := by
    intros; expose_names; exact (uniqueness_0 words_str _hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    (h_ens1_ret2 : ensures1 words_str ret2)
    : ensures2 words_str ret1 := by
    exact hpost1.2

theorem uniqueness_3
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    (h_ens1_ret2 : ensures1 words_str ret2)
    (h_ens2_ret1 : ensures2 words_str ret1)
    : ensures2 words_str ret2 := by
    intros; expose_names; exact (uniqueness_2 words_str _hpre ret2 ret1 hpost2 hpost1 h_ens1_ret2 h_ens1_ret1); done

theorem uniqueness_4
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    (h_ens1_ret2 : ensures1 words_str ret2)
    (h_ens2_ret1 : ensures2 words_str ret1)
    (h_ens2_ret2 : ensures2 words_str ret2)
    (h_extract_ret1 : extractWords ret1 = (extractWords words_str).reverse)
    (h_extract_ret2 : extractWords ret2 = (extractWords words_str).reverse)
    : extractWords ret1 = extractWords ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_5_0
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    (h_ens1_ret2 : ensures1 words_str ret2)
    (h_ens2_ret1 : ensures2 words_str ret1)
    (h_ens2_ret2 : ensures2 words_str ret2)
    (h_extract_ret1 : extractWords ret1 = (extractWords words_str).reverse)
    (h_extract_ret2 : extractWords ret2 = (extractWords words_str).reverse)
    (h_same_words : extractWords ret1 = extractWords ret2)
    (h_format_ret1 : isProperlyFormatted ret1 = true)
    (h_format_ret2 : isProperlyFormatted ret2 = true)
    : ∀ (s1 s2 : String), isProperlyFormatted s1 = true → isProperlyFormatted s2 = true → extractWords s1 = extractWords s2 → s1 = s2 := by
    sorry

theorem uniqueness_5
    (words_str : String)
    (_hpre : precondition words_str)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition words_str ret1)
    (hpost2 : postcondition words_str ret2)
    (h_ens1_ret1 : ensures1 words_str ret1)
    (h_ens1_ret2 : ensures1 words_str ret2)
    (h_ens2_ret1 : ensures2 words_str ret1)
    (h_ens2_ret2 : ensures2 words_str ret2)
    (h_extract_ret1 : extractWords ret1 = (extractWords words_str).reverse)
    (h_extract_ret2 : extractWords ret2 = (extractWords words_str).reverse)
    (h_same_words : extractWords ret1 = extractWords ret2)
    (h_format_ret1 : isProperlyFormatted ret1 = true)
    (h_format_ret2 : isProperlyFormatted ret2 = true)
    : ∀ (s1 s2 : String), isProperlyFormatted s1 = true → isProperlyFormatted s2 = true → extractWords s1 = extractWords s2 → s1 = s2 := by
    -- Introduce the universally quantified variables and hypotheses
    have h_intro : ∀ (s1 s2 : String), isProperlyFormatted s1 = true → isProperlyFormatted s2 = true → extractWords s1 = extractWords s2 → s1 = s2 := by
      (try simp at *; expose_names); exact (uniqueness_5_0 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1 h_ens1_ret2 h_ens2_ret1 h_ens2_ret2 h_extract_ret1 h_extract_ret2 h_same_words h_format_ret1 h_format_ret2); done
    exact h_intro

theorem uniqueness (words_str : String):
  precondition words_str →
  (∀ ret1 ret2,
    postcondition words_str ret1 →
    postcondition words_str ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the ensures1 conditions from both postconditions
  have h_ens1_ret1 : ensures1 words_str ret1 := by
    (try simp at *; expose_names); exact (uniqueness_0 words_str _hpre ret1 ret2 hpost1 hpost2); done
  have h_ens1_ret2 : ensures1 words_str ret2 := by
    (try simp at *; expose_names); exact (uniqueness_1 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1); done
  -- Extract the ensures2 conditions from both postconditions
  have h_ens2_ret1 : ensures2 words_str ret1 := by
    (try simp at *; expose_names); exact (uniqueness_2 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1 h_ens1_ret2); done
  have h_ens2_ret2 : ensures2 words_str ret2 := by
    (try simp at *; expose_names); exact (uniqueness_3 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1 h_ens1_ret2 h_ens2_ret1); done
  -- From ensures1, both extractWords results equal the same reversed list
  have h_extract_ret1 : extractWords ret1 = (extractWords words_str).reverse := by
    (try simp at *; expose_names); exact h_ens1_ret1; done
  have h_extract_ret2 : extractWords ret2 = (extractWords words_str).reverse := by
    (try simp at *; expose_names); exact h_ens1_ret2; done
  -- Therefore extractWords ret1 = extractWords ret2
  have h_same_words : extractWords ret1 = extractWords ret2 := by
    (try simp at *; expose_names); exact (uniqueness_4 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1 h_ens1_ret2 h_ens2_ret1 h_ens2_ret2 h_extract_ret1 h_extract_ret2); done
  -- Both ret1 and ret2 are properly formatted
  have h_format_ret1 : isProperlyFormatted ret1 = true := by
    (try simp at *; expose_names); exact h_ens2_ret1; done
  have h_format_ret2 : isProperlyFormatted ret2 = true := by
    (try simp at *; expose_names); exact h_ens2_ret2; done
  -- Key lemma: A properly formatted string is uniquely determined by its extracted words
  -- This is because a properly formatted string with words [w1, ..., wn] must be exactly
  -- "w1 w2 ... wn" (words joined by single spaces, no leading/trailing spaces)
  have h_unique_format : ∀ s1 s2 : String, isProperlyFormatted s1 = true → isProperlyFormatted s2 = true → extractWords s1 = extractWords s2 → s1 = s2 := by
    (try simp at *; expose_names); exact (uniqueness_5 words_str _hpre ret1 ret2 hpost1 hpost2 h_ens1_ret1 h_ens1_ret2 h_ens2_ret1 h_ens2_ret2 h_extract_ret1 h_extract_ret2 h_same_words h_format_ret1 h_format_ret2); done
  -- Apply the uniqueness lemma to conclude ret1 = ret2
  exact h_unique_format ret1 ret2 h_format_ret1 h_format_ret2 h_same_words
end Proof
