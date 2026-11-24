import YM.Heron.Dew
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open Finset
variable (χ:E4→ℝ)
-- charge linearity. Realm smooth only at active shell. guard.
abbrev Realm (χ:E4→ℝ)(j: Axis→E4→ℂ): Prop:=∀ i:Axis,Integrable fun x=> grad i χ x • j i x
variable {U V: Axis→E4→ℂ}(h:Realm χ U)(k: Realm χ V)
include h k
lemma realm_add : Realm χ (U+V):=by intro i; simp_rw [Pi.add_apply,smul_add]; exact (h i).add (k i)
lemma value_add : exportFlux (U+V) χ= exportFlux U χ+exportFlux V χ:=by unfold exportFlux; simp_rw[Pi.add_apply,smul_add, integral_add (h _) (k _), Finset.sum_add_distrib,neg_add]
lemma realm_sub : Realm χ (U - V):=by intro i; simp_rw [Pi.sub_apply,smul_sub]; exact (h i).sub (k i)
lemma value_sub : exportFlux (U-V) χ= exportFlux U χ-exportFlux V χ:=by unfold exportFlux; simp_rw[Pi.sub_apply,smul_sub, integral_sub (h _) (k _), Finset.sum_sub_distrib,neg_sub]; abel
omit h k
lemma valueM (c:ℂ): exportFlux (c • U) χ=c • exportFlux U χ:=by unfold exportFlux; simp only[Pi.smul_apply]; simp_rw [← smul_comm c, integral_smul,← Finset.smul_sum,smul_neg]
lemma value_neg : exportFlux (-U) χ= -exportFlux U χ:=by unfold exportFlux; simp_rw [Pi.neg_apply,smul_neg,integral_neg,Finset.sum_neg_distrib]
lemma ovum : Realm χ 0:=by simp [Realm]
lemma voidK : exportFlux (fun _ :Axis=> fun _=> (0:ℂ)) χ=0:=by simp [exportFlux]
include h
lemma realmK(c:ℂ):Realm χ (c • U):=by intro i; simp only [Pi.smul_apply]; simp_rw[← smul_comm c]; exact (h i).smul c
omit h
lemma shines {I:Type*} (L:List I) (f:I→List I→Axis→E4→ℂ) (H:∀ i v, Realm χ (f i v)): Realm χ (fun a y=>slips L (fun i l=> f i l a y)) ∧ exportFlux (fun a y=>slips L (fun i l=> f i l a y)) χ= slips L fun i l=> exportFlux (f i l) χ:=by
     induction L generalizing f with
     | nil=> simp_rw[slips_nil]; exact ⟨ovum χ,voidK χ⟩
     | cons a L ih=>
        obtain ⟨hQ,hV⟩:= ih (fun i t=> f i (a::t)) (fun i t=> H _ _); simp_rw[slips_cons]; let g(i:Axis)(y:E4):= slips L (fun i' l=>f i' (a::l) i y); refine ⟨realm_sub χ (H _ _) hQ,?_⟩; exact (value_sub χ (H a L) (show Realm χ g from hQ)).trans (congr_arg (fun x:ℂ=> _-x) hV)
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(hχ:Massive.Physics.Window x χ) (e:Flavor 6)(Δ:Ortho.Skew)(a b:Axis)
local notation "U0"=> tsupport (fderiv ℝ χ)
local notation "R"=> fromCenter Δ.val (x 0)
local notation "T"=> windD x Δ e
include hχ hx
lemma balmy (i j: Dot d) : Realm χ (T i j):=by
    obtain ⟨s,c⟩:=i; obtain ⟨t,b⟩:=j; obtain ⟨α₀,p,u,a,w,rfl⟩:=voicing c; obtain ⟨α₁,q,v,l,y,rfl⟩:= voicing b; change Realm χ (T (piD s _ p _ _ _) (piD t _ q _ _ _)); by_cases he: α₀=false∧α₁=true∧a=l∧w=e∧y=e; swap; · rw [dark x w y e Δ p q u v a l α₀ α₁ s t he]; exact ovum _
    obtain ⟨h1,h2,h3,h4,h5⟩:=he; subst α₀ α₁ l w y
    let f:=pose gamma (deck u) (steps p) (x s); let g:=pose (FlipT gamma) (deck v) (steps q) (x t); intro a'; let B:=brook gamma f g R; have hb:Integrable (fun y=> grad a' χ y • B a' y):= Maxwell.Free.shell_cost hχ.1 hχ.2.1 (fun y hy=> (bow gamma a' g f y _ (helm ..) (nicePose _ _ _ _ (palmG x hx y χ hχ hy s) _) (nicePose _ _ _ _ (palmG x hx y χ hχ hy t) _)).continuousAt) a'
    apply hb.congr; refine Eventually.of_forall fun y=>?_ ; by_cases hy:y∈ U0; · exact congr_arg (grad a' χ y • ·) (cruise x hx e Δ p q u v a χ hχ s t y hy a').symm
    simp [image_eq_zero_of_notMem_tsupport (f:=grad a' χ) (fun h=> hy (Maxwell.Free.gradient_part χ a' h))]
variable (p q:GPol)(u v:List (letters d))
local notation "W"=> tot u v
local notation "F_"=> ester x p q
local notation "L"=> fiesta x
local notation "Q"=>ballow p q u v
noncomputable def actS (x: Points 2)(Δ:Ortho.Skew)(u:Fin 2→ Pol d)(r:Axis×Axis→ Label 8)(i:Axis)(y:E4):ℂ:=∑ j:Axis, fromCenter Δ.val (x 0) j y • trioL y x u (r (i,j)).val
set_option quotPrecheck false
local notation "X"=> actS x Δ Q (Massive.Tawny.Cast.Carnal.sunS e).val
set_option quotPrecheck false
local notation "F" i:arg => ester x p q * fiesta x i
lemma they (a:Axis)(y:E4)(hy:y∈U0): X a y= - slips W (fun i z=> slips z (fun j w=> T i j a y *(ester x p q* fiesta x w))) :=by
   unfold actS; simp_rw [fun j:Axis=> liftBD x y hx (torchD x hx y χ hχ hy) p q u v a j e,smul_neg, Finset.sum_neg_distrib, slips,Finset.smul_sum]; congr 1; rw[Finset.sum_comm]; apply sum_congr rfl; intro i _; rw[Finset.sum_comm]; apply sum_congr rfl; intro j _; unfold windD; simp_rw [smul_eq_mul, Complex.real_smul,Finset.sum_mul,Finset.mul_sum]; apply sum_congr rfl; intro k _; ring
lemma prices : exportFlux X χ= -dualD W (fun i j w=> combD x Δ e i j χ* (F w)):=by
    let U(i j:Dot d)(t:List (Dot d))(b:Axis)(y:E4):=windD x Δ e i j b y * (F t); let Q':=fun (b:Axis)(y:E4)=>slips W (fun i z=> slips z (fun j w=> U i j w b y));
    rw [show exportFlux X χ= exportFlux (-Q') χ from ?_,value_neg];
    · have hf(i j t) : U i j t=(F t) • T i j:=by funext b y; exact mul_comm ..
      have ht i j t: Realm χ (U i j t):=by rw[hf]; exact realmK χ (balmy χ x hx hχ e Δ _ _) _
      have hp(i z):= shines χ z (U i) (ht i); have hy:= shines χ W (fun i z a y=> slips z (fun j w=>U i j w a y)) (fun i z=>(hp i z).1)
      rw [show exportFlux Q' χ= _ from hy.2]; apply congr_arg; simp_rw [fun i z=>(hp i z).2]; unfold dualD; simp_rw [hf,valueM]; simp only [smul_eq_mul]; -- slips defs?
      simp_rw [show ∀ i j:Dot d, exportFlux (T i j) χ=combD x Δ e i j χ from fun i j=>rfl]; unfold slips; apply Finset.sum_congr rfl; intro i _; apply congr_arg; apply Finset.sum_congr rfl; intro j _; apply congr_arg; exact mul_comm ..
    unfold exportFlux; congr 1; apply sum_congr rfl; intro i _; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ ; by_cases he:y∈ U0; · exact congr_arg (grad i χ y •·) (they χ x hx hχ e Δ p q u v _ _ he)
    simp [image_eq_zero_of_notMem_tsupport (f:=grad i χ) (fun h=> he (Maxwell.Free.gradient_part χ i h))]
end YM.Heron
#print axioms YM.Heron.prices
