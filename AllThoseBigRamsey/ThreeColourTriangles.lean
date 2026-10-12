import AllThoseBigRamsey.TriangleRepair

/-!
# Three-colour triangle certificates

Colours are 0,1,2. Bits of the palette correspond, in this order, to
000,001,002,011,012,022,111,112,122,222. SmallSAP tests actual one-point
amalgamation spans over at most three base vertices. The manuscript proves
that these tests characterize strong amalgamation for triangle classes.

For each of 106 palettes, a base-three integer stores the 27 values of a
triangle-repair operation. Six further palettes are colour permutations of
169. All finite claims use kernel `decide`, not native_decide or external
solver results. The generator is not part of the trusted proof.
-/
namespace AllThoseBigRamsey.ThreeColourTriangles

abbrev Colour := Fin 3

def triangleIndex (a b c : Colour) : Nat :=
  let zeros := (if a.val = 0 then 1 else 0) + (if b.val = 0 then 1 else 0) +
    (if c.val = 0 then 1 else 0)
  let ones := (if a.val = 1 then 1 else 0) + (if b.val = 1 then 1 else 0) +
    (if c.val = 1 then 1 else 0)
  if zeros = 3 then 0 else if zeros = 2 then (if ones = 1 then 1 else 2)
  else if zeros = 1 then (if ones = 2 then 3 else if ones = 1 then 4 else 5)
  else if ones = 3 then 6 else if ones = 2 then 7 else if ones = 1 then 8 else 9

def Triangle (palette : Fin 1024) (a b c : Colour) : Prop :=
  palette.val.testBit (triangleIndex a b c) = true

def SmallSAP (palette : Fin 1024) : Prop :=
  (∀ a b : Colour, ∃ t : Colour, Triangle palette a b t) ∧
  (∀ edge p₀ p₁ q₀ q₁ : Colour,
    Triangle palette edge p₀ p₁ → Triangle palette edge q₀ q₁ →
    ∃ t : Colour, Triangle palette p₀ q₀ t ∧ Triangle palette p₁ q₁ t) ∧
  (∀ ab ac bc p₀ p₁ p₂ q₀ q₁ q₂ : Colour,
    Triangle palette ab ac bc →
    Triangle palette ab p₀ p₁ → Triangle palette ac p₀ p₂ → Triangle palette bc p₁ p₂ →
    Triangle palette ab q₀ q₁ → Triangle palette ac q₀ q₂ → Triangle palette bc q₁ q₂ →
    ∃ t : Colour, Triangle palette p₀ q₀ t ∧ Triangle palette p₁ q₁ t ∧
      Triangle palette p₂ q₂ t)

def repairData (palette : Fin 1024) : Nat :=
  match palette.val with
  | 57 => 8523700416
  | 63 => 8136259509
  | 127 => 8137853832
  | 173 => 143154531540
  | 191 => 39569931777
  | 233 => 146255495589
  | 237 => 143156125863
  | 251 => 134231266299
  | 255 => 39571526100
  | 299 => 1129703875104
  | 319 => 1043969506932
  | 327 => 3943933137867
  | 338 => 3865172351593
  | 351 => 3861292884141
  | 355 => 1129710724707
  | 359 => 1126611354981
  | 361 => 3671576277822
  | 362 => 3671576080978
  | 363 => 1129705469427
  | 375 => 1043976356535
  | 383 => 1043971101255
  | 447 => 1075403179200
  | 454 => 3902039112397
  | 455 => 3902039112396
  | 474 => 3896600768581
  | 475 => 3896600768571
  | 478 => 3896213347372
  | 479 => 3892726556409
  | 489 => 3629682252351
  | 505 => 3617658042759
  | 506 => 3617658023062
  | 507 => 3617658023061
  | 510 => 3617270601853
  | 511 => 1075404773523
  | 575 => 5091867916167
  | 639 => 5091869510490
  | 647 => 7479352893423
  | 653 => 7479348898122
  | 655 => 7479348701025
  | 660 => 7375768648442
  | 671 => 7375764298359
  | 681 => 6924565965456
  | 684 => 6921466600112
  | 685 => 5226886188198
  | 695 => 5123305780833
  | 703 => 5123301588435
  | 710 => 7479350767660
  | 711 => 7479350767659
  | 716 => 7479350492453
  | 717 => 7479350492445
  | 718 => 7479350472739
  | 719 => 7479350295348
  | 734 => 7473525002635
  | 735 => 7375765892682
  | 745 => 6924564371133
  | 748 => 6921465005789
  | 749 => 5226887782521
  | 767 => 5123303182758
  | 809 => 6213435728859
  | 811 => 6213435531762
  | 829 => 6190549415673
  | 831 => 6127701163590
  | 838 => 6768228502679
  | 839 => 6768228502677
  | 866 => 6213442381375
  | 867 => 6213442381365
  | 870 => 6212667538949
  | 871 => 6210343011639
  | 873 => 6213442106151
  | 874 => 6213441909307
  | 875 => 6213437126085
  | 886 => 6190556344115
  | 887 => 6127708013193
  | 895 => 6127702757913
  | 902 => 6726350951879
  | 903 => 6726350951877
  | 937 => 6182024377113
  | 948 => 6159139185941
  | 949 => 6159139185933
  | 950 => 6159139146518
  | 951 => 6159139028256
  | 953 => 6159912906339
  | 956 => 6159138063929
  | 957 => 6159138063927
  | 958 => 6159138024506
  | 959 => 6159134835858
  | 966 => 6443904940726
  | 967 => 6443904940725
  | 986 => 6438466596910
  | 987 => 6438466596909
  | 988 => 6438079195415
  | 990 => 6438079175701
  | 991 => 6438079175700
  | 1001 => 6171548080680
  | 1010 => 6159912394621
  | 1012 => 6159137060177
  | 1013 => 6159137591616
  | 1014 => 6159137552195
  | 1015 => 6159137552193
  | 1017 => 6159523871088
  | 1018 => 6159523851391
  | 1019 => 6159523851390
  | 1020 => 6159136449896
  | 1021 => 6159136469604
  | 1022 => 6159136430182
  | 1023 => 6159136430181
  | _ => 0

def repair (palette : Fin 1024) (c a h : Colour) : Colour :=
  ⟨(repairData palette / 3 ^ (9 * c.val + 3 * a.val + h.val)) % 3,
    Nat.mod_lt _ (by decide)⟩

def ChecksRepair (palette : Fin 1024) : Prop :=
  (∀ c a h : Colour, Triangle palette c a (repair palette c a h)) ∧
  (∀ c a h : Colour, Triangle palette c a h → repair palette c a h = h) ∧
  (∀ c a a' h h' t : Colour, Triangle palette a a' t → Triangle palette h h' t →
    Triangle palette (repair palette c a h) (repair palette c a' h') t)

def Exceptional (palette : Fin 1024) : Prop :=
  palette.val = 169 ∨ palette.val = 297 ∨ palette.val = 326 ∨
  palette.val = 354 ∨ palette.val = 646 ∨ palette.val = 652

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certified_classification : ∀ palette : Fin 1024,
    SmallSAP palette ↔ (ChecksRepair palette ∨ Exceptional palette) := by
  unfold SmallSAP ChecksRepair Exceptional Triangle
  decide

theorem repair_or_exception (palette : Fin 1024) (h : SmallSAP palette) :
    (∃ r, TriangleRepair.Laws (Triangle palette) r) ∨ Exceptional palette := by
  rcases (certified_classification palette).mp h with hc | he
  · exact Or.inl ⟨repair palette, ⟨hc.1, hc.2.1, hc.2.2⟩⟩
  · exact Or.inr he

/-- The six permutations, encoded by their three base-three digits. -/
def rename (i : Fin 6) (a : Colour) : Colour :=
  let code := match i.val with
    | 0 => 21 | 1 => 15 | 2 => 19 | 3 => 7 | 4 => 11 | _ => 5
  ⟨(code / 3 ^ a.val) % 3, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exceptional_renaming : ∀ palette : Fin 1024, Exceptional palette →
    ∃ i : Fin 6,
      (∀ a b : Colour, rename i a = rename i b → a = b) ∧
      ∀ a b c : Colour,
        Triangle palette a b c ↔
        Triangle ⟨169, by decide⟩ (rename i a) (rename i b) (rename i c) := by
  unfold Exceptional Triangle
  decide

theorem diagonal_obstruction : ∀ d : Colour,
    ¬ (Triangle ⟨169, by decide⟩ 1 1 d ∧ Triangle ⟨169, by decide⟩ d d 2) := by
  decide

/-- The exceptional palette genuinely needs the different finite-quotient proof. -/
theorem exceptional_has_no_repair (r : Colour → Colour → Colour → Colour) :
    ¬ TriangleRepair.Laws (Triangle ⟨169, by decide⟩) r := by
  intro h
  exact diagonal_obstruction (r 1 1 1)
    ⟨h.lands 1 1 1, h.pairs 1 1 1 1 1 2 (by decide) (by decide)⟩

end AllThoseBigRamsey.ThreeColourTriangles
