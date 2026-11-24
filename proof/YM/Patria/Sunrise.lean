import YM.Patria.Depth
/-! Recovery average through all stages.Poster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d:ℕ}
variable (A:Run S N r 6)(hA:A.Actual)
local notation "Bn" => S.side r N
variable (B: Cover → Insertion (S.side r N) 6)
local notation "Q" => ratioTo S N
variable {m i:ℕ}
abbrev visitor (S:Scheme)(N i:ℕ){r:Side}(u:Averaging)(b:Cover)(B: Cover→ Insertion (S.side r N) 6): Insertion (S.side r N) 6:= Averaging.filter u (ratioTo S N i) B (ratioTo S N i • b)
local notation "V₀"=> Insertion (S.side r N) 6
variable (X₀: Insertion (S.side r N) 6) (u:Averaging)(b:Cover)
local notation "Vs" m b => visitor S N m u b B
abbrev trolley (u: Averaging)(i:ℕ)(b:Cover): Insertion (S.side r i) 6:= AllAt A i (A.regulator.density * visitor S N i u b B)
local notation "Sn" =>A.regulator.density
local notation "TP"=> trolley A B u
local notation "TX"=>AllAt A
open TorusPCAC.Geometry Exposure
open Rolls
local notation "Ds"=> stitch S r m
lemma visit_eq {I:Type}[Fintype I](p:I→ℝ)(t:I→ Cover)(hi:i<N)(hf:∀ (v:Cover→ Insertion (S.side r N) 6)(b:Cover), Averaging.filter u (S.step i).L.val v b= ∑ j,p j • v (b+t j)): visitor S N i u b B=∑ j,p j • visitor S N (i+1) u ((S.step i).L.val • b + t j) B:=by unfold visitor; rw [step_factor hi, invite _ u _ b _ (odd_to hi) (S.step _).odd,hf]
lemma trailer {I:Type}[Fintype I](p:I→ℝ)(t:I→ Cover)(hi:m<N)(hf:∀ (v:Cover→ Insertion (S.side r N) 6)(b:Cover), Averaging.filter u (S.step m).L.val v b= ∑ j,p j • v (b+t j)): ⇑(TP m b)=∑ j,(p j:ℂ) • A.block m (TP (m+1) ((S.step m).L.val • b+t j)) :=by
    unfold trolley; rw [visit_eq B u b p t hi hf,mul_sum]; simp_rw [mul_smul_comm]; let W(j):= (S.step m).L.val • b+t j; let F(j):= Sn*visitor S N (m+1) u (W j) B
    change ⇑(TX m (∑ j,p j • F j))= _; rw [map_sum]; funext x; rw [ContinuousMap.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j _
    rw [show (TX m) (p j • F j)=_ from map_smul ((TX m).restrictScalars ℝ) (p j) (F j)]; exact congr_arg ((p j:ℂ) • ·) (congr_fun (route A (F j) hi) x) -- terse
lemma boarding : TP N b = Sn * B b :=by unfold trolley visitor; rw [origin,centreN,one_smul, roles,chain_zero]; rfl
abbrev localEye (V:Grid Bn) (b:Cover): Insertion Bn 6 →ₗ[ℝ] Fields Bn 6:= (((crank 1 1 (wrap _ b) (heat b)).toLinearMap.comp (ContinuousMap.evalCLM ℂ (pull 1 (wrap _ b) V)).toLinearMap).restrictScalars ℝ)
lemma trail (x:Averaging)(b a:Cover)(h:∀ b c,march c (B b)=B (b+c)) : march a ⇑(Averaging.filter x i B b)= ⇑(Averaging.filter x i B (b+a)):=by
     rw [roles]; funext V; let F(A:Cover) := localEye (S:=S) V a (B A); let G : Insertion Bn 6→ₗ[ℝ] Fields Bn 6:= (ContinuousMap.evalCLM ℝ V).toLinearMap -- field guess
     have hh:F=fun b'=> G (B (b'+a)):=funext fun i=> congr_fun (h i a) V
     change localEye (S:=S) V a _= _; rw [rollLinear]; change rolls 1 i (menu x) F b=G _; rw [hh, rollLinear]; exact driftRoll (fun i=> G (B i)) b _ _ _ -- sig
include hA in
lemma axial (h:∀ b c,march c (B b)=B (b+c))(a b:Cover)(hi:i≤N): march a (TP i b)=TP i (b+a):=by
     refine journey A _ _ a hi ?_; unfold visitor; simp_rw [smul_add]; let k:= Q i • b; let L:= Q i • a; have hx:= trail B u k L (i:=Q i) h; have hy:= move_pivot A.regulator L rfl; funext V; exact (map_mul (crank 1 1 (wrap _ L) (heat L)) ..).trans (congr_arg₂ HMul.hMul (congr_fun hy V) (congr_fun hx V))
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.axial
#print axioms YM.Massive.Patria.Depth.trailer
