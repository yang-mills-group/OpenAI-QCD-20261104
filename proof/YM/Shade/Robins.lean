import YM.Shade.Dove
import YM.Shade.Belt
/-! Literal uniform cost readings used in mixture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Massive.Fir Fir YM.Fir.NoteF Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Choir
variable {Q: Choir}
variable (H:Q.Harmony P φ)
namespace Measures
set_option maxHeartbeats 720000

variable {d k:ℕ}(w:Label d)(r:Averaging)(v:Label k)(y:ℕ→Label k)(hx:Tendsto y atTop (𝓝 v)) (A:Set E4)(x:E4)
private def duo (x:Label k) (i:Fin 2):Label ((![d,k]:Fin 2→ℕ) i):= Fin.cases (motive:=fun j:Fin 2=>Label ((![d,k]:Fin 2→ℕ) j)) w (Fin.cases (motive:=fun i:Fin 1=>Label ((![d,k]:Fin 2→ℕ) i.succ)) x (fun i=>Fin.elim0 i)) i
lemma yards (i:ℕ)(b:Cover) : pollF C 2 i ![0,b]= arm (digit (C.S.spacing (C.N i)) b):=by ext1 j; rw [arm_l]; fin_cases j; exact digit_zero _; rfl
include H hx hφ
open Needle.GaugeP
lemma pricedQ (hA:IsCompact A) (hB:0∉A)(ε:ℝ)(he:0<ε):∀ᶠ i in atTop,∀ p:Cover, digit (C.S.spacing (C.N (φ i))) p∈ A → ‖rod2 C (φ i) (stem P d (φ i) w) ((stemV P k (φ i) r (y (φ i))) p) - ans2 (Q.focus none d w) (Q.focus r k v) (digit (C.S.spacing (C.N (φ i))) p)‖ ≤ ε:=by
      let D:Fin 2→ℕ:=![d,k]; let G:Fin 2→ Averaging:=![none,r]; let Y:=(fun i=> duo w (y (φ i))); let B:=duo w v; let F := eyeW P D G
      let V(t:Points 2):ℂ:= Q.total 2 t (fun j=>Q.focus (G j) _ (B j))
      have hy:Tendsto Y atTop (𝓝 B):=tendsto_pi_nhds.mpr fun i=> by fin_cases i; exact tendsto_const_nhds; exact hx.comp hφ
      let K:= arm '' A; have ht:K⊆ conf 2:=by rintro _ ⟨x,h,rfl⟩; exact forms (fun he=>hB (he ▸ h))
      have hv:= compactity K (hA.image arm.continuous) (show ContinuousOn V K from ((H.h.smooth _ _).continuousOn.mono ht)) (fun x hp=> H.exposed D G B Y hy x (ht hp)) ε he
      filter_upwards [hv] with i hi p hp; let j:=φ i; let x:= digit (C.S.spacing (C.N j)) p; have ht':pollF C 2 (φ i) ![0,p]∈ K:= ⟨x,hp,(yards (φ i) p).symm⟩; have hl:= hi ![0,p] ht'; rw [dist_eq_norm] at hl; change ‖eyeW P D G j ![0,p] (Y i)- V (pollF C 2 j ![0,p])‖ ≤ _ at hl
      have hh : eyeW P D G j ![0,p] (Y i)= rod2 C j (stem P d j w) ((stemV P k j r (y j)) p) :=by
           change (C.A j).regulator.average (List.ofFn (fun t:Fin 2=> stemV P (D t) j (G t) (Y i t) ((![0,p] :Fin 2→ Cover) t))).prod= _; simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; rfl
      rw [hh,yards] at hl; unfold V at hl; rw [show (fun t:Fin 2=>Q.focus (G t) _ (B t))=![Q.focus none d w,Q.focus r k v] from (funext fun i=>by fin_cases i <;> rfl)] at hl; exact hl
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.pricedQ
