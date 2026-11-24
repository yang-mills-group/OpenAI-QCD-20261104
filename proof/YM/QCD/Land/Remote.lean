import YM.QCD.Land.Demand

/-! # Thermodynamic limits robust to finite shifts of antiperiodic seams -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Land
open Lat Lattice RP Wilson Grass Function Extraction Filter Topology BigOperators
open Finset
open scoped Matrix.Norms.Frobenius Matrix
variable {β m : ℝ} {F : ℕ} {n : Side}

def seamPoint (z : Cover) (t : ℕ) (a : Axis) : Per (spanT t) := (half t).val + (z a:ℤ)
def relay (F : ℕ) (β m : ℝ) (z : Cover) (t : ℕ) : Lat.Cut (spanT t) F := ⟨β,seamPoint z t,m⟩

lemma base_billed (t) : relay F β m 0 t=bill F β m t := by
  unfold bill relay; congr 1; funext i; simp [seamPoint]

def sep (a : ℤ) (t : ℕ) : Per (spanT t) := (half t).val + a
lemma duration (i k : ℤ) : ∀ᶠ t : ℕ in atTop,
    ((i : Per (spanT t))-sep k t).val = ((half t).val+(i-k) : ℤ).toNat := by
  filter_upwards [half_trend.eventually (eventually_gt_atTop (i-k).natAbs)] with t ht
  let f : ℤ := (half t).val+(i-k)
  have hi : 0 ≤ f := by unfold f; omega
  have hx : f.toNat < (spanT t).val := by unfold f; rw [twice]; omega
  have he : (2:Per (spanT t))*(half t).val=0 := by rw [← Nat.cast_ofNat (n:=2),← Nat.cast_mul, ← twice, ZMod.natCast_self]
  rw [show (i : Per (spanT t))-sep k t=(f.toNat:Per (spanT t)) by
    rw [← Int.cast_natCast (R:= Per (spanT t)) f.toNat,Int.toNat_of_nonneg hi]
    unfold f sep; push_cast; rw [two_mul] at he
    calc
      _ = ((i: Per (spanT t)) - k) - ((half t).val: Per (spanT t)) := by abel
      _ = _ := by
        rw [sub_eq_add_neg]; -- check direction
        nth_rw 1 [show ((half t).val:Per (spanT t))= - ((half t).val:Per (spanT t)) from eq_neg_of_add_eq_zero_left he]; abel,
    ZMod.val_natCast_of_lt hx]

lemma distant (x : Cover) (a : Axis) (z : Cover) : ∀ᶠ t in atTop, seam (seamPoint z t) (wrap (spanT t) x) a=1 := by
  let i := x a+1
  filter_upwards [duration i (z a),half_trend.eventually (eventually_gt_atTop (i-z a).natAbs)] with t ht hb
  apply if_neg; intro h
  change ((x a:ℤ):Per (spanT t))+1=sep (z a) t at h
  rw [show ((i:ℤ):Per (spanT t))=sep (z a) t by unfold i; push_cast; exact h,sub_self,ZMod.val_zero] at ht
  omega

lemma highrank {b a : ℤ} (h : b<a) (t : ℕ) (ht : (b-a).natAbs < (spanT t).val) :
    (sep b t-sep a t).val=(spanT t).val-(b-a).natAbs := by
  have hi : (spanT t).val-(b-a).natAbs < (spanT t).val := by omega
  rw [← ZMod.val_natCast_of_lt hi]
  apply congrArg ZMod.val
  rw [Nat.cast_sub ht.le,ZMod.natCast_self]
  rw [← Int.cast_natCast (R:=Per (spanT t)) (b-a).natAbs, show (((b-a).natAbs:ℕ):ℤ)=a-b by omega]
  unfold sep; push_cast; ring
lemma lowrank {b a : ℤ} (h : a≤b) (t : ℕ) (ht : (b-a).natAbs < (spanT t).val) :
    (sep b t-sep a t).val=(b-a).natAbs := by
  rw [← ZMod.val_natCast_of_lt ht]; apply congrArg ZMod.val; rw [← Int.cast_natCast (R:=Per (spanT t)) (b-a).natAbs, show (((b-a).natAbs:ℕ):ℤ)=b-a by omega]
  unfold sep; push_cast; ring

def axisTape (i : Axis) (a b : ℤ) (t : ℕ) : Tape (spanT t) := ⟨i,sep a t, sep b t⟩
lemma near_stamp (i : Axis) (a b : ℤ) (x : Cover) : ∀ᶠ t : ℕ in atTop,
    (axisTape i a b t).stamp (wrap (spanT t) x) = if a≤b then 1 else -1 := by
  let d := x i-a
  filter_upwards [half_trend.eventually (eventually_gt_atTop (d.natAbs+(b-a).natAbs)), duration (x i) a] with t ht he
  have hn : (b-a).natAbs < (spanT t).val := by rw [twice]; omega
  have hd : (d.natAbs+(b-a).natAbs)<(half t).val := ht
  change (if ((x i : Per (spanT t))-sep a t).val < (sep b t-sep a t).val then -1 else (1:ℂ))=_
  rw [he]
  unfold d at *
  by_cases h : a≤b
  · rw [if_pos h,lowrank h t hn,if_neg (by omega)]
  rw [if_neg h,highrank (by omega) t hn,twice,if_pos (by omega)]


-- grade parity disappears in expectation (both normalized and not)
def imprint (x : Insertion n F) : Insertion n F := ⟨fun U => grade (x U), grade.toLinearMap.continuous_of_finiteDimensional.comp x.continuous⟩
lemma ber_grade_apply {X : Type*} [Fintype X] (x : Dirac X) : ber X (grade x)=ber X x := by
  have ht := odd_loss (minus_grade x)
  conv_lhs => rw [← both x, map_add, map_add,(show grade (plus x)=_ from plus_grade _), (show grade (minus x)=_ from minus_grade _),map_neg,ht,neg_zero]
  nth_rw 2 [← both x] -- check
  rw [map_add,ht]
lemma imprinting (C : Lat.Cut n F) (x : Insertion n F) : C.average (imprint x)=C.average x := by
  have he (U) : C.rate (imprint x) U=C.rate x U := by
    unfold Lat.Cut.rate
    congr 1; rw [← ber_grade_apply ((C.insertD*x) U)]
    simp only [ContinuousMap.mul_apply,map_mul, (show grade (C.insertD U)=_ from gauss_plus _)]
    rfl
  simp only [Lat.Cut.average, LinearMap.smul_apply]; congr 1; unfold Lat.Cut.raw
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [he]

lemma roll_local_plus {D : Lot} (T : Tape n) (h : ∀ i : Court D,T.stamp (wrap n i.val)=1) (x : Cyl D F) :
    T.roll (issue n x)=issue n x := by
  ext1 U; simp only [Tape.rolls,issued]
  apply AlgHom.congr_fun (φ₁ := (T.tape F).comp (pass (allot n)))
  apply ext_atoms; rintro (i|i)
  · change T.tape F (pass _ (psi i))=pass _ (psi i)
    simp [allot,h]
  change T.tape F (pass _ (bar i))=pass _ (bar i); simp [allot,h]
lemma roll_local_minus {D : Lot} (T : Tape n) (h : ∀ i : Court D,T.stamp (wrap n i.val)= -1) (x : Cyl D F) :
    T.roll (issue n x)=imprint (issue n x) := by
  ext1 U
  change T.tape F (pass (allot n) (x _))=grade (pass (allot n) (x _))
  apply AlgHom.congr_fun (φ₁ := (T.tape F).comp (pass (allot n))) (φ₂ := grade.comp (pass (allot n)))
  apply ext_atoms; rintro (i|i)
  · change T.tape F (pass _ (psi i))=grade (pass _ (psi i))
    simp only [pass_psi,Tape.tape_psi,psi,grade_atom]; simp [allot,h]
  change T.tape F (pass _ (bar i))=grade (pass _ (bar i)); simp only [pass_bar,Tape.tape_bar,bar,grade_atom]; simp [allot,h]

lemma shifts (u : Cover) (i : Axis) (b : ℤ) (t : ℕ) :
    relay F β m (Function.update u i b) t=(axisTape i (u i) b t).swap (relay F β m u t) := by
  unfold relay Tape.swap; congr 1
  funext a
  simp only [axisTape,seamPoint,sep]
  by_cases h : a=i
  · simp [h]
  simp [h,seamPoint]
lemma destination (u : Cover) (t : ℕ) :
    (relay F β m u t).partitionR=(bill F β m t).partitionR := by
  let S (s : Finset Axis) (i : Axis) : ℤ := if i ∈ s then u i else 0
  have hg (s : Finset Axis) : (relay F β m (S s) t).partitionR=(bill F β m t).partitionR := by
    induction s using Finset.induction_on with
    | empty => simp only [S,notMem_empty,ite_false]; exact congrArg Lat.Cut.partitionR (base_billed t)
    | @insert i s hi ih =>
      rw [show S (insert i s) = Function.update (S s) i (u i) from funext fun x => by rcases eq_or_ne x i with h|h <;> simp [S,h]]
      rw [shifts,Tape.roll_normer _ _ rfl]; exact ih
  simpa only [S,mem_univ,if_true] using hg univ

lemma compare (i : Axis) (b : ℤ) (u : Cover) (D : Lot) :
    ∀ᶠ t in atTop, tally (relay F β m (Function.update u i b) t) D=tally (relay F β m u t) D := by
  have he : ∀ᶠ t in atTop,∀ k : Court D,(axisTape i (u i) b t).stamp (wrap (spanT t) k.val) = if u i≤b then 1 else -1 := eventually_all.mpr (fun k => near_stamp i (u i) b k.val)
  filter_upwards [he] with t ht
  ext1 x
  rw [shifts]; simp only [tallying]; let T := axisTape i (u i) b t
  rw [← Tape.roll_average T (relay F β m u t) rfl]
  by_cases h : u i≤b
  · rw [roll_local_plus T (D:=D) (fun k => by simpa [T,h] using ht k)]
  rw [roll_local_minus T (D:=D) (fun k => by simpa [T,h] using ht k), imprinting]
lemma equality (u : Cover) (D : Lot) : ∀ᶠ t in atTop,tally (relay F β m u t) D=tally (bill F β m t) D := by
  let S (s : Finset Axis) (i : Axis) : ℤ := if i ∈ s then u i else 0
  have he (s : Finset Axis) : ∀ᶠ t in atTop,tally (relay F β m (S s) t) D=tally (bill F β m t) D := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [S,notMem_empty,ite_false]; apply Eventually.of_forall; intro t
      change tally (relay F β m 0 t) D=_; rw [base_billed]
    | @insert i s hi ih =>
      rw [show S (insert i s) = Function.update (S s) i (u i) from funext fun x => by rcases eq_or_ne x i with h|h <;> simp [S,h]]
      filter_upwards [ih,Land.compare (F:=F) (β:=β) (m:=m) i (u i) (S s) D] with k hk ht; exact ht.trans hk
  simpa only [S,mem_univ,if_true] using he univ

lemma world {D : Lot} (x : Cyl D F) {k : Extraction.Sequence} {f : LocalState F} (h : Exhausts β m k f)
    (u : Cover) : Tendsto (fun t => tally (relay F β m u (k t)) D x) atTop (𝓝 (f.amp D x)) :=
  (h D x).congr' ((k.cofinal.eventually (equality u D)).mono (fun _ h => LinearMap.congr_fun h.symm _))
end YM.QCD.Land
