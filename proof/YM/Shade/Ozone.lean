import YM.Oriole.Visee
import YM.Dart.Falls
import YM.Differ.Tull
/-
  Vanishing authentic baskets at common observer maturity. Parallel
  deterministic Tally information retained, to match difference charges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}
local notation "S"=> C.S
set_option quotPrecheck false
open CardsT Rolls
variable (u:Averaging)(w:(i:ℕ)→stalk C i)
abbrev Knoll (C:Sequence)(i j ℓ:ℕ)(x:stalk C i)(u:Averaging)(v:ℝ):Prop:=∀ (hj:j≤ℓ)(hp:ℓ≤ C.N i)(he:Even ((C.R i).val)),let R:= C.R i; ∀ z:Site (C.S.side R ℓ),∀ y:Site (C.S.side R j),∀ b:Cover,wrap _ b∈ (mural (viewW C.S R hj) (evenW C.S R he j) z).margin y (Tarot.Vista.marginM C.S 16 j ℓ) → Gold (C.A i).regulator (Column.sky C.S R j (C.N i) (hj.trans hp) (evenW C.S R he j) z) y (CardsT.checkedT u (ratioTo C.S (C.N i) ℓ) x b) v
variable {i ℓ j:ℕ}
lemma tickM (x y:stalk C i)(b:Cover):checkedT u j (x+y) b=checkedT u j x b+checkedT u j y b:=by unfold checkedT; simp_rw [roles]; rw[training]; rfl
lemma chimes (x:stalk C i)(z:ℂ)(b:Cover):checkedT u j (z • x) b=z • checkedT u j x b:=by
      unfold checkedT; rw[roles,roles]; exact (rollLinear (v:=x) (M:=j) (k:=1) (l:=menu u) (j • b) ((z • (LinearMap.id (R:=ℂ) (M:=Insertion (C.S.side (C.R i) (C.N i)) 6))).restrictScalars ℝ)).symm
variable {u}
namespace Knoll
variable {x y:stalk C i}{c b:ℝ}(h:Knoll C i j ℓ x u c)(z:ℂ)
include h
lemma more (hb:c≤b):Knoll C i j ℓ x u b:= fun v t he x y b hB=> Gold.mono (h v t he x y b hB) hb
lemma got (h':Knoll C i j ℓ y u b):Knoll C i j ℓ (x+y) u (c+b):=by intro v t he R Z Y W ht; rw[tickM]; exact Gold.together (h v t he Z Y W ht) (h' v t he Z Y W ht)
lemma owns : Knoll C i j ℓ (z • x) u (‖z‖*c) :=by intro v t he R Z Y W ht; rw[chimes]; exact Gold.minted (h v t he Z Y W ht) z
end Knoll
lemma quotaY {c:Side}(V X:Density c 6)(x:Label d)(H: SourceRead.TaperHol)(b:Cover)(t:ℂ)(h:Tally H b x V X) : Tally H b (t • x) V (t • X):=by
    have he:= Orientation.acting H b d (Canvas.foil V X) x.val h.sees t; refine ⟨h.unit,?_⟩; change Beacon.ActionTest H b (Canvas.foil V (t • X)) _; rw [show Canvas.foil V (t • X)= t • Canvas.foil V X from (by funext U; simp [Canvas.foil,mul_smul_comm])]; exact he
lemma totalY {c:Side}(V X Y:Density c 6)(x y:Label d)(H: SourceRead.TaperHol)(b:Cover)(h:Tally H b x V X)(he:Tally H b y V Y) : Tally H b (x+y) V (X+Y):=by
     have ht:= tally_sub _ _ _ _ _ _ _ h (quotaY V Y y H b (-1) he); rw[neg_one_smul,neg_one_smul,sub_neg_eq_add,sub_neg_eq_add] at ht; exact ht
variable (L:ℕ→ℕ)(Θ:SourceRead.TaperHol)(m:ℕ)
structure Weave (u:Averaging) (w:(i:ℕ)→stalk C i)(x:ℕ→ Label d):Prop where
     sees :∀ᶠ i in atTop, Tally Θ 0 (x i) ((C.A i).density m) (trolley (C.A i) (w i) u m 0)
     lands :∀ᶠ j in atTop,∃ F:ℕ→ℝ,Tendsto F atTop (𝓝 0)∧ ∀ᶠ i in atTop,0≤ F i ∧Knoll C i j (L j) (w i - stemV P d i u (x i)) u (F i)
namespace Weave
variable {w} {Γ:(i:ℕ)→stalk C i}{x y:ℕ→ Label d}{P L Θ m}
variable (hx:Weave P L Θ m u w x)(hy:Weave P L Θ m u Γ y)
include hx hy
lemma together : Weave P L Θ m u (w+Γ) (x+y):=by
    constructor
    · filter_upwards [hx.sees,hy.sees] with i hi hj; rw [Pi.add_apply,Pi.add_apply,treadM]; exact totalY _ _ _ _ _ _ _ hi hj
    filter_upwards [hx.lands,hy.lands] with j hj hm; obtain ⟨F,hF,h⟩:= hj; obtain ⟨G,hG,hM⟩:= hm; refine ⟨fun i=> F i + G i,by simpa only [zero_add] using hF.add hG,?_⟩; filter_upwards [h,hM] with i ht hp; refine ⟨add_nonneg ht.1 hp.1,?_⟩; rw [Pi.add_apply,Pi.add_apply,map_add, add_sub_add_comm]; exact Knoll.got ht.2 hp.2
omit hy
lemma raises (f:ℂ): Weave P L Θ m u (f • w) (f • x):=by
    constructor
    · filter_upwards [hx.sees] with i hi; rw [Pi.smul_apply,Pi.smul_apply,scopeY]; exact quotaY _ _ _ _ _ _ hi
    filter_upwards [hx.lands] with j hj; obtain ⟨F,hF,h⟩:= hj; refine ⟨fun i=> ‖f‖ * F i,by simpa only[mul_zero] using hF.const_mul _,?_⟩; filter_upwards [h] with i hi; rw [Pi.smul_apply,Pi.smul_apply,map_smul, ← smul_sub]; exact ⟨mul_nonneg (norm_nonneg _) hi.1,Knoll.owns hi.2 f⟩
lemma graduated {I:Type*}(s:Finset I)(X:I→(i:ℕ)→stalk C i)(v:I→ℕ→ Label d)(hp:∀ i∈s, Weave P L Θ m u (X i) (v i)): Weave P L Θ m u (∑ i∈s,X i) (∑ i∈s,v i):=by
    induction s using Finset.induction_on with
    | empty=> rw[sum_empty,sum_empty]; simpa only [zero_smul] using hx.raises 0
    | insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact together (hp a (mem_insert_self ..)) (ih fun i hi=>hp i (mem_insert_of_mem hi))
end Weave
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Weave.graduated
