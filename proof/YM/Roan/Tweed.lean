import YM.Roan.Lear
import YM.Rill.Comes
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Tarn.ChargeQ
open Function Set Filter
open Lattice Wilson QCD QCD.Lat
open UV Patria Patria.Depth Patria.Hub Poised Poised.Plans Poised.Plans.Stamp
open Choir Choir.Strip Quilt Massive.Patria.Gall Massive.Patria.Gall.Onyx
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix.Norms.Frobenius InnerProductSpace
variable {C:Sequence}{P:Calibration C}{K:Choir}{φ:ℕ→ℕ}{β e:ℝ}(hp:C.Path β e)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable (F:Pollens P K)(hf:Foil P K F)(HQ:K.Harmony P φ)
variable (x y:E4)(a b:Axis)
local notation "S"=> K.total
include hp hP hφ HQ F
open Finset
variable (v w: K.W)
local notation "T"=> (0:Fin 2)
local notation "x'"=> points ![x,y]
local notation "sg"=> signT (Signed.mirror b) a
local notation "tQ"=> Signed.reflect b
local notation "N" p:arg=> Ortho.move tQ p
local notation "J"=> F.adj b
lemma housing (z:Points 2)(i:Axis): points (![z 0,z 1])=z:=by apply PiLp.ext; intro i; fin_cases i<;>rfl
lemma tint_deriv: F.adj b (K.arc a v)=(sg:ℂ) • K.arc a (F.adj b v):=by
        apply HQ.h.same; intro p he x; obtain ⟨z,hz,rfl⟩:= Choir.affined (Signed.reflect b) Fin.revPerm p he -- check.XYX
        obtain ⟨w,rfl⟩:= (J).surjective x; let x₁:=points fun i:Fin 2=> Ortho.move (Signed.reflect b) (z (Fin.revPerm i))
        have hxS : z 0≠ z 1:=fun h=> (show (0:Fin 2)≠1 from by decide) (hz h)
        have hg:=reversal hp hP hφ F HQ (z 0) (z 1) a b v w hxS; rw[(housing hp hP hφ F HQ z b)] at hg
        have hR:=HarmonyF.swung hp HQ hφ hP F z hz (![K.arc a v,w]) b; have ht: HarmonyF.tilted b z=points ![N (z 1),N (z 0)]:=by apply PiLp.ext; intro i; fin_cases i<;>rfl
        change S _ (HarmonyF.tilted b z) ![J w, _]= S 2 (HarmonyF.tilted b z) ![J w,_]; rw [ht,hg,← hR,ht,show ⇑(F.adj b) ∘ _ ∘ _= _ from (?_ : ⇑(F.adj b) ∘ (![K.arc a v,w])∘ Fin.rev = ![J w,F.adj b (K.arc a v)])]; funext i; fin_cases i<;>rfl
include hf
local notation "ω" => lampU P K
open HarmonyF
local instance choirXX (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
set_option maxHeartbeats 800000 in
lemma k_zero : K.arc a ω=0:=by
       apply (F.adj a).injective; rw[map_zero]; apply HQ.h.same; intro p he y; obtain ⟨z,hz,rfl⟩:=affined (Signed.reflect a) Fin.revPerm p he; obtain ⟨w,rfl⟩:=(F.adj a).surjective y; let X:= (![K.arc a ω,w]); have h := swung hp HQ hφ hP F z hz X a
       have he(zp:Points 2):Fin.cons (F.adj a w) ![(F.adj a (K.arc a ω))] = (F.adj a) ∘ X∘ Fin.rev :=by funext i; fin_cases i<;>rfl
       let k':=(fun A:Points 2=> K.total 2 A (![ω,w])); have he': S 2 z X=0:=by
           let t(δ:ℝ):=points ![z 0 + δ • basis a,z 1]; have hT:t 0=z:=by unfold t; simp; exact housing hp hP hφ F HQ z a -- fix
           have hx:HasDerivAt t (Points.direction (0:Fin 2) a) 0:= shore hp hP hφ F HQ _ _ a
           have hP':k'∘t=ᶠ[𝓝 0] (fun _=> S 1 (points ![z 1]) (![w])):= (hx.continuousAt.eventually ((show t 0∈ conf 2 from hT.symm ▸ hz)|> (conf_open _).mem_nhds)).mono fun δ hδ=>by
                change _=_; exact (hf.functor 1 (t δ) hδ (![w])).trans (by apply congr_arg (fun x=>S 1 x _); apply PiLp.ext; intro i; fin_cases i; rfl)
           have hv:= ear_t HQ a ω w z hz t (0:Fin 2) 1 hT (by simpa only [one_smul] using hx)  -- rewrite fragile
           have h':HasDerivAt (fun x:ℝ=> S 1 (points (![z 1])) (![w])) (K.total 2 z X) 0:=by apply HasDerivAt.congr_of_eventuallyEq _ hP'.symm; rw [one_smul, update0] at hv; exact hv
           exact h'.unique (hasDerivAt_const ..)
       rw [he', star_zero] at h; change S 2 (tilted a z) (![F.adj a w,F.adj a (K.arc a ω)])=S 2 _ (![F.adj a w,0]); rw [show (![F.adj a w,F.adj a (K.arc a ω)])=_ from (he z),h]; exact ((S 2 _).map_coord_zero (1:Fin 2) rfl).symm -- arg
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.k_zero
#print axioms YM.Massive.Tarn.ChargeQ.tint_deriv
