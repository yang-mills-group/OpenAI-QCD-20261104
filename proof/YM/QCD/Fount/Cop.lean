import YM.QCD.Fount.Stout
/-! # Chalice receipts. at all aux. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings
variable {J b l n N:ℕ}{p:Clip}{r D R A v t s η K Y Z B θ δ z C τ w α:ℝ}{c f:Side}{S:StepData c f}
local notation "Vp"=> (fun i:Positions (Primary c su)=> represent (Uniform.tint su _ i))
section frob
open scoped Matrix.Norms.Frobenius
-- outer Mode entire unit
lemma stove (hp : PaintSupply su l z) {x:Positions (Primary c su)}(hx:‖x‖≤1): Mode (G:=su) Vp x l ((1+outerCost su l z)*1):=by
   refine ⟨(by have ht:=outer_pos su l hp.1; positivity),fun i=>?_⟩
   let j:= (i.1,Exterior.coord i.2); let o := Exterior.Body 1 c
   let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : o => su.Color) j ∘L (tint su o).toContinuousLinearMap
   have hQ : ‖L‖≤ Uniform.shade su := ContinuousLinearMap.opNorm_le_bound _ (Uniform.shade_pos _).le fun v=> le_trans (norm_le_pi_norm (tint su o v) _) (Uniform.tint_le v)
   have hL : ‖L x‖ ≤ Uniform.shade su := (L.le_opNorm x).trans ((mul_le_mul hQ hx (norm_nonneg x) (Uniform.shade_pos _).le).trans_eq (mul_one _))
   have he: Allows l (fun v=>su.mat (Vp v i)) x (outerCost su l z):=by
        have hh v : Vp v i=su.lieExp (L v) := Work.F03.represent_link _ _
        simp_rw [hh]; exact (hp.2 _ hL).comp (allows_linear hQ hL)
   exact thicken (Brush.offer.2 ⟨he.1.of_le le_top,he.2⟩)
end frob
variable (k': BareRates.pre su τ C J) {x: Positions (Primary c su)}
lemma grantS {R':PathData su}(hr:R'.Bounds p τ C w)(hp:1≤Y)(hz:(Fintype.card (Primary c su):ℝ)≤ Y)(hx: ‖x‖<1)(hh:0≤w) (he:|α|≤ K):
   let S:= fun z : Positions (Primary c su)=> α*secondTerm p R' (Vp z); ContDiffAt ℝ ω S x ∧ ∀ i:ℕ, i ≤ J → 0 < i → normJ i S x≤ tollS Y J ((1+K+w)*BareRates.bill k' p)+tollS Y J ((1+|0|+w)*BareRates.bill k' p) :=by
   let F t := draft (c:=c) t R' p ∘ tint su _; intro S
   have ht:S=F α-F 0:=funext fun i=>by simp [S,F,draft]
   have HX:= mem_ball_zero_iff.mpr hx; obtain ⟨-,hf,h,hV,-,hK⟩:=bareSocket c k' hr HX α; have hh':=bareSocket c k' hr HX 0
   have ht₀ : ContDiffAt ℝ ω (F 0) x:=hh'.2.1
   rw [ht]; refine ⟨hf.sub ht₀,fun i hi hi'=>?_⟩
   rw [normJ,iteratedFDeriv_sub_apply (hf.of_le le_top) (ht₀.of_le le_top)]
   have h'':= ratifyS hp hz h (by positivity) hK hi hi'
   apply (norm_sub_le ..).trans; refine add_le_add (h''.trans ?_) (ratifyS hp hz h (by positivity) hh'.2.2.2.2.2 hi hi'); unfold tollS; gcongr
open scoped Matrix.Norms.L2Operator
lemma portrait {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{D:Grid c→Sheet c}{Q:E→Grid c}{x:E} (h:Own c t 0 b D v)(ht:0<t)(hv:0≤v)(he:Mode (G:=su) Q x l Z): Brush l (clump l ((massQ+massQ)*(1+Z)^l) (letterP t l*v)) 1 (D ∘ Q) x:=by
   obtain ⟨U,V,h⟩:=h; let g:=Kit.settled∘ Q; have hp {i}(hi:i∈ball (g x) t): i∈Kingdom c t:= Set.mem_iUnion.mpr ⟨_,hi⟩
   have hz:= composite (retro he|>.trim) (beau (x:=g x) ht (fun _ hi=>h.won _ (hp hi)) (fun _ hi=> h.empire le_rfl hv _ (hp hi)) l)
   exact hz.shimmy (Eventually.of_forall fun i=> Eq.symm (h.winched ..))
abbrev chord (t B z:ℝ)(l:ℕ):= clump l ((massQ+massQ)*(1+(1+outerCost su l z)*1)^l) (letterP t l*B)
lemma cited {W:ℕ→Atom su 2}(hs:Own c t 0 b (robe W) B)(hv:0≤B)(hx:‖x‖≤1)(ht:0<t)(hp:PaintSupply su l z)(hd:(Fintype.card (Site c):ℝ) ≤ Y): Brush l ((Y*Fintype.card Lat.Fiber)*chord t B z l) 1 (Extra.Iteration.action W∘Vp) x:=by
   have hu:= (portrait hs ht hv (stove hp hx)).report (alti c) ((ascent c).trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)))
   exact hu.shimmy (Eventually.of_forall fun i=> (reporting ..).symm)
def levy (a B t R Z Y z v:ℝ)(l:ℕ)(s:ℝ)(N:ℕ):= (s^2*Y^2)*chord a B z l+ N*(v+(Z*Fintype.card Lat.Fiber)*chord t R z l)
lemma coda {X:PathData su}(hr:X.Bounds p τ C w)(hp:1≤Y)(hz:(Fintype.card (Primary c su):ℝ)≤Y)(hx:‖x‖<1)(hh:0≤w)(he:|α|≤ K) {D:Grid c→Sheet c}{W:ℕ→Atom su 2}
   (hs:Own c η 0 n D B)(hv:0≤B)(hη:0<η)(hk:Own c t 0 b (robe W) R)(ht:0<t)(ha:0≤R)(h₁:(Fintype.card (Site c):ℝ)≤Y)(hK: (Fintype.card (Lat.Modes c N):ℝ) ≤ A)(h₂:0<s)(hc: PaintSupply su l z) (hl: l≤J)(hg:0<l):
   let W':= chalice X p W α D N s ∘ Vp; ContDiffAt ℝ l W' x ∧ normJ l W' x ≤ levy η B t R Y A z (tollS Y J ((1+K+w)*BareRates.bill k' p)+tollS Y J ((1+|0|+w)*BareRates.bill k' p)) l s N:=by
   intro Z; have hv':= (portrait hs hη hv (stove hc hx.le)).report (powerZ c N s) ((billed h₂ c N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hK _) (sq_nonneg _)))
   have ht:= grantS k' hr hp hz hx hh he
   let S i:=α*secondTerm p X (Vp i); let F:=Extra.Iteration.action W ∘ Vp; have hS:= cited hk ha hx.le ‹0<t› hc h₁ -- binder
   let Q:= (N:ℝ) • (S + F); let f' := baker c N ∘ Q
   have hf:ContDiffAt ℝ (↑l) S x:=ht.1.of_le le_top
   have he':ContDiffAt ℝ (↑l) (S+F) x:=hf.add hS.smooth
   have hQ:ContDiffAt ℝ l Q x:= ContDiffAt.const_smul (N:ℝ) he' -- inspect
   have hK':ContDiffAt ℝ l f' x:= (baker c N).contDiff.contDiffAt.comp _ hQ
   refine ⟨hv'.smooth.sub hK',?_⟩
   rw [normJ, show iteratedFDeriv ℝ l Z x= _ from iteratedFDeriv_sub_apply hv'.smooth hK']; apply (norm_sub_le ..).trans; apply add_le_add ((Brush.offer.1 hv').2 l le_rfl)
   refine ((baker c N).norm_iteratedFDeriv_comp_left hQ (n:=l) le_rfl).trans ((mul_le_of_le_one_left (norm_nonneg _) (colP ..)).trans ?_); unfold Q; rw [iteratedFDeriv_const_smul_apply he',norm_smul, Real.norm_of_nonneg (by positivity), iteratedFDeriv_add_apply hf hS.smooth]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact (norm_add_le ..).trans (add_le_add (ht.2 l hl hg) ((Brush.offer.1 hS).2 l le_rfl))
end YM.QCD.Fount
