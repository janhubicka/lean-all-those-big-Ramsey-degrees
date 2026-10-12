import AllThoseBigRamsey.TriangleRepair

/-!
# Exhaustive three-colour triangle certificates

Colour triples are numbered 000,001,002,011,012,022,111,112,122,222.
Repair tables are encoded in base three, least significant digit first,
with index 9*s+3*x+h. An obstruction code is
n + 4*(base + 27*(p + 27*q)), where base,p,q are three base-three digits.
The base digits name edges 01,02,12; unused coordinates are ignored.
All finite checks below use kernel reduction, not native_decide.
These are certificates about triangle predicates and small strong-amalgamation
requests. The class-level TRAP bridge is a separate written proof.
-/
namespace AllThoseBigRamsey.ThreeColourCertificates
open TriangleRepair
abbrev Colour := Fin 3

def trit (code i : Nat) : Colour :=
  ⟨(code / 3^i) % 3, Nat.mod_lt _ (by decide)⟩

def tripleIndex (a b c : Colour) : Nat :=
  let lo := min a.val (min b.val c.val)
  let hi := max a.val (max b.val c.val)
  let mid := a.val + b.val + c.val - lo - hi
  match lo, mid, hi with
  | 0, 0, 0 => 0 | 0, 0, 1 => 1 | 0, 0, 2 => 2
  | 0, 1, 1 => 3 | 0, 1, 2 => 4 | 0, 2, 2 => 5
  | 1, 1, 1 => 6 | 1, 1, 2 => 7 | 1, 2, 2 => 8
  | _, _, _ => 9

def Triangle (mask : Nat) (a b c : Colour) : Prop :=
  mask.testBit (tripleIndex a b c) = true

instance (mask : Nat) (a b c : Colour) : Decidable (Triangle mask a b c) := by
  unfold Triangle
  infer_instance

def rule (code : Nat) (s x h : Colour) : Colour :=
  trit code (9*s.val+3*x.val+h.val)

def RepairLaw (mask code : Nat) : Prop :=
  (∀ s x h : Colour, Triangle mask s x (rule code s x h)) ∧
  (∀ s x h : Colour, Triangle mask s x h → rule code s x h = h) ∧
  (∀ s x y h k d : Colour,
    Triangle mask x y d → Triangle mask h k d →
    Triangle mask (rule code s x h) (rule code s y k) d)

def repairData : Array (Nat × Nat) := #[
  (57,8523700416),(63,8136259509),(127,8137853832),
  (173,143154531540),(191,39569931777),(233,146255495589),
  (237,143156125863),(251,134231266299),(255,39571526100),
  (355,1129710724707),(359,1126611354981),(363,1129705469427),
  (375,1043976356535),(383,1043971101255),(447,1075403179200),
  (511,1075404773523),(639,5091869510490),(711,7479350767659),
  (719,7479350295348),(735,7375765892682),(749,5226887782521),
  (767,5123303182758),(1023,6159136430181)
]

def obstructionData : Array (Nat × Nat) := #[
 (0,1),(1,2917),(2,5833),(3,5833),(6,3025),(7,3025),
 (9,5833),(10,5833),(11,5833),(12,5941),(13,5941),(14,5941),
 (15,5941),(16,1),(17,3025),(18,3025),(19,3025),(22,3025),
 (23,3025),(25,6049),(26,6049),(27,6049),(28,6049),(29,6049),
 (30,6049),(31,6049),(40,1),(41,5941),(42,5941),(43,5941),
 (46,5941),(47,5941),(56,1),(58,9074),(59,14906),(62,9074),
 (65,2917),(67,5833),(68,2917),(69,2917),(70,5941),(71,5941),
 (75,5833),(76,5941),(77,5941),(78,5941),(79,5941),(81,6049),
 (83,6049),(84,6049),(85,6049),(86,6049),(87,6049),(91,6049),
 (92,6049),(93,6049),(94,6049),(95,6049),(97,2917),(98,5941),
 (99,5941),(100,2917),(101,2917),(102,5941),(103,5941),(104,1),
 (105,5941),(106,5941),(107,5941),(108,5941),(109,5941),(110,5941),
 (111,5941),(113,21170),(114,23654),(115,23654),(116,18146),
 (117,21062),(118,17822),(119,21170),(120,1),(121,12318),
 (122,23654),(123,23654),(124,18146),(125,12314),(126,17822),
 (134,6049),(135,6049),(141,6049),(142,6049),(143,6049),
 (150,6049),(151,6049),(157,6049),(158,6049),(159,6049),
 (162,9074),(163,9074),(166,23654),(167,23654),(171,23654),
 (172,18146),(174,23654),(175,23654),(178,9074),(179,9074),
 (182,18146),(183,21170),(185,21066),(187,68367),(188,18146),
 (189,21062),(190,18146),(197,2917),(199,6049),(207,6049),
 (213,6049),(215,6049),(223,6049),(225,2917),(227,23654),
 (229,2917),(230,23654),(231,23654),(235,23654),(236,18146),
 (238,23654),(239,23654),(241,21170),(243,21170),(245,21062),
 (246,18146),(247,21170),(249,21066),(252,18146),(253,21062),
 (254,18146),(353,2917),(357,2917),(358,58611),(365,12314),
 (366,12314),(367,12314),(369,9082),(371,55443),(373,21062),
 (374,60411),(379,68367),(381,66747),(382,56523),(430,63543),
 (431,59619),(446,63543),(485,2917),(487,12322),(495,59619),
 (501,21062),(503,42087),(577,2917),(579,5833),(583,5941),
 (587,5833),(589,5941),(591,5941),(593,20414),(595,20414),
 (599,21170),(603,21170),(605,12314),(607,21170),(617,5941),
 (619,5941),(623,5941),(633,12318),(635,23654),(727,41871),
 (739,23654),(743,23654),(751,23654),(755,73875),(759,68619),
 (765,66747),(1007,59619)
]

def repairEntry (i : Fin 23) : Nat × Nat := repairData[i.val]!
def obstructionEntry (i : Fin 184) : Nat × Nat := obstructionData[i.val]!

def edge (b : Colour → Colour) (i j : Colour) : Colour :=
  if i.val = 0 then (if j.val = 1 then b 0 else b 1) else b 2

def ValidBase (mask n : Nat) (b : Colour → Colour) : Prop :=
  n < 3 ∨ Triangle mask (b 0) (b 1) (b 2)

def ValidType (mask n : Nat) (b p : Colour → Colour) : Prop :=
  ∀ i j : Colour, i.val < j.val → j.val < n → Triangle mask (edge b i j) (p i) (p j)

/-- Actual one-point strong-amalgamation requests over bases of size at most 3. -/
def SmallSAP (mask : Nat) : Prop :=
  ∀ n : Nat, n ≤ 3 → ∀ b p q : Colour → Colour,
    ValidBase mask n b → ValidType mask n b p → ValidType mask n b q →
    ∃ d : Colour, ∀ i : Colour, i.val < n → Triangle mask (p i) (q i) d

def Obstruction (mask code : Nat) : Prop :=
  let n := code % 4
  let b := fun i : Colour => trit (code / 4) i.val
  let p := fun i : Colour => trit (code / 108) i.val
  let q := fun i : Colour => trit (code / 2916) i.val
  1 ≤ n ∧ n ≤ 3 ∧ ValidBase mask n b ∧
  ValidType mask n b p ∧ ValidType mask n b q ∧
  (∀ d : Colour, ∃ i : Colour, i.val < n ∧ ¬ Triangle mask (p i) (q i) d)

theorem obstruction_not_smallSAP {mask code : Nat} (hw : Obstruction mask code) :
    ¬ SmallSAP mask := by
  intro hs
  rcases hw with ⟨_, hn, hb, hp, hq, hbad⟩
  obtain ⟨d, hd⟩ := hs _ hn _ _ _ hb hp hq
  obtain ⟨i, hi, hf⟩ := hbad d
  exact hf (hd i hi)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every stored repair satisfies all three laws, including equal type labels. -/
theorem repair_certificates_checked :
    ∀ i : Fin 23, RepairLaw (repairEntry i).1 (repairEntry i).2 := by
  unfold RepairLaw
  decide

/-- Every rejected representative has an explicit nonamalgamable request. -/
theorem obstruction_certificates_checked :
    ∀ i : Fin 184, Obstruction (obstructionEntry i).1 (obstructionEntry i).2 := by
  unfold Obstruction ValidBase ValidType
  decide

def certifiedSystem (i : Fin 23) : RepairSystem Colour (Triangle (repairEntry i).1) where
  repair := rule (repairEntry i).2
  valid := (repair_certificates_checked i).1
  fixed := (repair_certificates_checked i).2.1
  pairs := (repair_certificates_checked i).2.2

/-- The six permutations, in lexicographic order, encoded by their three images. -/
def permutationCodes : Array Nat := #[21,15,19,7,11,5]
def permute (j : Nat) (a : Colour) : Colour := trit (permutationCodes[j]!) a.val

/-- The corresponding permutations of the ten unordered triangle indices. -/
def trianglePermutationCodes : Array Nat :=
  #[9876543210,6789345120,9520841736,259148376,6310742859,136247589]

def renamed (mask j : Nat) : Nat :=
  (List.range 10).foldl (fun acc i =>
    if mask.testBit i then
      acc + 2^((trianglePermutationCodes[j]! / 10^i) % 10)
    else acc) 0

def canonical (mask : Nat) : Nat × Nat :=
  (List.range 6).foldl (fun best j =>
    let candidate := renamed mask j
    if candidate < best.2 then (j,candidate) else best) (0,mask)

def RelabellingCorrect (mask : Nat) : Prop :=
  let j := (canonical mask).1
  let rep := (canonical mask).2
  j < 6 ∧
  (∀ a b : Colour, permute j a = permute j b → a = b) ∧
  (∀ a : Colour, ∃ b : Colour, permute j b = a) ∧
  (∀ a b c : Colour, Triangle mask a b c ↔
    Triangle rep (permute j a) (permute j b) (permute j c))

/-- No palette is lost when passing to a representative under colour renaming. -/
theorem relabellings_checked : ∀ mask : Fin 1024, RelabellingCorrect mask.val := by
  unfold RelabellingCorrect
  decide

def Classified (rep : Nat) : Prop :=
  (∃ i : Fin 23, (repairEntry i).1 = rep) ∨ rep = 169 ∨
  (∃ i : Fin 184, (obstructionEntry i).1 = rep)

/-- All 1024 palettes are covered by repair, the square, or a genuine obstruction. -/
theorem classification_checked : ∀ mask : Fin 1024, Classified (canonical mask.val).2 := by
  unfold Classified
  decide

/-- An explicit semantic consequence of the obstruction certificates. -/
theorem classified_smallSAP (mask : Fin 1024)
    (hs : SmallSAP (canonical mask.val).2) :
    (∃ i : Fin 23, (repairEntry i).1 = (canonical mask.val).2) ∨
    (canonical mask.val).2 = 169 := by
  rcases classification_checked mask with hr | he | ho
  · exact Or.inl hr
  · exact Or.inr he
  · obtain ⟨i, hi⟩ := ho
    have hw := obstruction_certificates_checked i
    rw [hi] at hw
    exact False.elim (obstruction_not_smallSAP hw hs)

end AllThoseBigRamsey.ThreeColourCertificates
