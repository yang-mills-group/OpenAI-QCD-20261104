import YM.Eole.Revenue
import YM.Eole.Pulse
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
local notation "ξ"=> Stitch.Tablet.credits
local notation "ω" i:arg=> payU (shore a i) (∏ j∈i,heightE P.order z j) P
variable {ν w B' Ω δ y η:ℝ} (hv:1≤ w)(hT:0<t)
include hv hT
open Push.AbsoluteSums.Trees
local notation "zH"=> heightE P.order z
variable (hr:Ready a P.B (QCD.GasP.taxed (swatch Y) (heightE P.order z) w) (α+η) ν b δ) (hp:0 ≤ α)(hη:0<η)
include hr hp hη
open Reserves
noncomputable def rentM (B k m:ℕ)(b:ℝ):ℝ:=(4*(B:ℝ)+2)^(2+m*k)*polyPrice b (2+m*k)
local notation "D'"=>ν*(1-δ)⁻¹
local notation "C"=>rentM P.B P.order P.power η
lemma filling : Setting W g Y q o p old a f (heightE P.order z) P t:=by
    have hm (i):z i ≤ zH i:= le_mul_of_one_le_left (positiveZ W g Y q o p old a f z h hT i) (one_le_pow₀ (by norm_num))
    refine { h with borne := fun i x=> (h.borne _ _).trans (hm _), each:= ?_ }; intro i j hx; obtain ⟨r,hp0,H,Kv,hu,he⟩:=h.each i j hx; exact ⟨r,hp0,H,fun i ht l he hz=> (Kv _ ht l he hz).trans (hm _),hu,he.trans (hm _)⟩
lemma feeds : Ac.Hit (fun i:Cand W g Y=> shore a i.val) P.B (fun i:Cand W g Y=> ∏ j∈i.val,(heightE P.order z) j) (α+η) (ν*(1-δ)⁻¹):=by
   let e : L ↪ Finset N:= ⟨Subtype.val,Subtype.val_injective⟩; let k i:= flagsOf Y (e i)
   have hh:=revenues W g Y q o p old a f (heightE P.order z) (filling W g Y q o p old a f z h hv hT hr hp hη) hr (add_nonneg hp hη.le) hv hT e k (fun _=>rfl) (fun i=> packet W g Y q o p old a f z h i.val i.2.1.1) -- include hv order. 
   have hx(i:L): taxed k (fun i=> ∏ j∈e i,zH j) w i=∏ j∈e i,zH j:=by rw [taxed,show k i= ∅ from (empty_dim W g Y i).2,card_empty,pow_zero,one_mul]
   unfold Ac.Hit; unfold Ac.Hit at hh; simp_rw [hx] at hh; exact hh
lemma flair : Ac.Hit (fun i:Cand W g Y=> shore a i.val) P.B (fun i:Cand W g Y=> ω (i.val)) α (C* (ν*(1-δ)⁻¹)):=by
     have hx:= feeds W g Y q o p old a f z h hv hT hr hp hη
     intro x; have hz:= positiveZ W g Y q o p old a f z h hT; have hr(i):0 ≤ zH i:=mul_nonneg (pow_nonneg (by norm_num) _) (hz _); have hJ(i:L):0 ≤ ∏ j∈i.val,zH j:=prod_nonneg fun j _=>hr j; have hP:0 ≤ C:= by unfold rentM; unfold Reserves.polyPrice; positivity
     refine budget_mono (budget_scale hP (hx x)) (fun i=>ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (show 0 ≤ 1+(wag (shore a i.val) P.B:ℝ) from by positivity) _) (hJ _)) (Real.exp_pos _).le) le_rfl) fun i=> ?_
     split; next hi=>
        let V:= shore a i.val; let s:ℝ:=coverNumber P.B V; let w:=1+(wag V P.B:ℝ); let D:= 2+P.power*P.order; have hb: w ≤ (4*(P.B:ℝ)+2)*(1+s):=by unfold w wag s; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) P.B]
        have he :w^D≤ C*Real.exp (η*s):=by
              refine (pow_le_pow_left₀ (by unfold w; positivity) hb D).trans ?_; rw [mul_pow]; exact (mul_le_mul_of_nonneg_left (polynomial_cost hη (show 0 ≤ s from Nat.cast_nonneg _) D) (show 0 ≤ (4* (P.B:ℝ)+2)^D by positivity)).trans_eq (mul_assoc ..|>.symm)
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (hJ _)) (show 0 ≤ Real.exp (α*s) from (Real.exp_pos _).le)).trans_eq (by change C*Real.exp (η*s)*(∏ j∈i.val, zH j)*Real.exp (α*s)= C*((∏ j∈i.val,zH j)*Real.exp ((α+η)*s)); rw [add_mul,Real.exp_add]; ring)
     rw [mul_zero]
-- realize E receipt
omit hr hp hη hv hT
private lemma earnsN (i:Cand W g Y) : Nonempty J:=by obtain ⟨j,_⟩:=lightD W g Y h.ear i; exact ⟨j⟩
noncomputable def fred (h:∀ i:E,(g (.inl i)).Nonempty)(i:L): J:= (lightD W g Y h i).choose
local notation "r" i:arg=>fred W g Y h.ear i
lemma fed(i:L): p (fred W g Y h.ear i)∈ shore a i.val:= rays W g Y q o p old a f z h _ (mem_image_of_mem _ (lightD W g Y h.ear i|>.choose_spec))
noncomputable def lucida (h:Setting W g Y q o p old a f z P t) :Reel c 6 J (Cand W g Y):=⟨fun i=>⟨p (fred W g Y h.ear i),shore a i.val,fed W g Y q o p old a f z h i⟩,fun i=> glowT W g i.val,fun i=>journal W g q f i.val⟩
local notation "LM"=> lucida W g Y q o p old a f z h
include hv hT hr hp hη
lemma lifeE : (lucida W g Y q o p old a f z h).Occupant p (W.flag q) t P 2 α (rentM P.B P.order P.power η*(ν*(1-δ)⁻¹)) (fun _=>1):=by
     refine ⟨⟨lightD W g Y h.ear,fun i=> rays W g Y q o p old a f z h _,fun i=>measurableJ W g Y q o p old a f z h _,fun i=>moodU W g Y q o p old a f z h _,fun i=>litter W g Y q o p old a f z h _ i.2.1.2.1,fun i=> glory W g Y q o p old a f z h i.val⟩,fun i=> ω (i.val), ?_,fun i j he=> haloG W g Y q o p old a f z h hT i _ (rays W g Y q o p old a f z h _ (mem_image_of_mem _ he))⟩
     simp only[abs_one,prod_const_one,one_mul]; exact flair W g Y q o p old a f z h hv hT hr hp hη
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.lifeE
