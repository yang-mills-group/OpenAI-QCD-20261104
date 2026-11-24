import YM.Tarn.Trust
/-! Non-null and honest rank, with all derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
variable {Z:SpaceZ}(H:Ability P φ Z)(h:Cresc Z){M:∀ d:ℕ,Axis→Label d→ₗ[ℂ] Label (d+2)} (he:Gains M Z)
variable (s: Sash G φ) (hz:DriftF G φ)
include hφ hp hr s H
lemma cant (v:foliage Z)(hv:v≠0):∃ x:E4,(∀ a:Axis,0<x a)∧∃ w:foliage Z,sphere Z h 2 (points ![0,x]) ![w,v] ≠ 0:=by
     obtain ⟨i,p,hp'⟩:= h.sealed v; have he' := LinearMap.mem_range_self (plume Z i) p; rw [← rafters hp hr hφ H s i, hp'] at he'; obtain ⟨k,hk⟩:= he'; have hK:k ≠0:=fun h0=>hv <| hk.symm.trans (by rw[h0,map_zero]); obtain ⟨j,hj⟩:= not_forall.mp (fun h=> hK (known hp hφ s H i h))
     let V:= (G i).K.coast; let Jq:= (G i).J; have hh(a:Axis):0<Jq.a a:= lt_of_lt_of_le (mul_pos (by norm_num: (0:ℝ)<2) Jq.far) ((Jq.pose _ (closedBall_mem_nhds _ Jq.breadth|> mem_of_mem_nhds)).2.1 a)
     let T':= s.L i j; let w:=plume Z i T'; refine ⟨V,fun a=> mul_pos (G i).K.pos (hh a),w,?_⟩; rw [cosmos Z (stage G i) h (fun s'=>⟨i,((![T',s.R i k]) s')⟩) _ ?_]; exact hj; intro k; fin_cases k; rfl; exact hk
omit hp hφ hr s H
variable (t:Fin n→foliage Z)
include he
local instance glassN (n:ℕ):ContinuousSMul ℝ (Points n):=inferInstance -- Does include he?
lemma gloss : ContDiffOn ℝ ∞ (fun x=> sphere Z h n x t) (conf n):=by
    choose p hp using fun i=>h.bell (t i); exact (he.smooth p).congr (fun x hx=> cosmos _ hx h p t hp)
include hp H hr G hφ
lemma sheen (l:ℕ):∃ m:ℕ,∃ A:ℝ,0 ≤ A ∧ ∀ r:ℝ,0 < r → r ≤ 1 →∀ x:Points n, spaced r x → ‖iteratedFDeriv ℝ l (fun x=> sphere Z h n x t) x‖ ≤ A *r⁻¹^m:=by
    choose p hy using fun i=> h.bell (t i); obtain ⟨m,A,hA,hV⟩:= temper hp hr hφ H (G:=G) he p l
    refine ⟨m,A,hA,fun r hR hx x hX=>?_⟩; have he : (fun y=> sphere Z h n y t) =ᶠ[𝓝 x] handle Z p:=by filter_upwards [(conf_open n).mem_nhds (spaced_conf hR hX)] with i hi; exact cosmos _ hi _ _ _ hy
    rw [(he.iteratedFDeriv ℝ l).eq_of_nhds]; exact hV r hR hx x hX
omit hp H hr G hφ
lemma bearings (F:Axis→foliage Z→ₗ[ℂ]foliage Z)(L:∀ d a p,F a (plume Z d p)=plume Z (d+2) (M d a p))(x:Points n)(hx:x∈conf n)(p:Fin n)(a:Axis) : D (Points.direction p a) (fun y=>sphere Z h n y t) x=sphere Z h n x (Function.update t p (F a (t p))):=by
    choose v hv using fun i=>h.bell (t i); have hK:(fun y=>sphere Z h n y t)=ᶠ[𝓝 x] handle Z v:=by filter_upwards [(conf_open n).mem_nhds hx] with y hy; exact cosmos _ hy h v t hv
    rw [GermD _ hK, he.openD x hx]; symm; refine cosmos Z hx h _ _ ?_; intro i; by_cases hr:i=p
    · subst i
      rw[Function.update_self]; change signets Z (Function.update v p ⟨(v p).1+2,M _ a (v p).2⟩ p)=_; rw [Function.update_self,← hv p]; exact (L _ _ _).symm
    change signets Z (Function.update v p _ i)=_; rw[update_of_ne hr,update_of_ne hr]; exact hv i
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.gloss
#print axioms YM.Massive.Tarn.sheen
#print axioms YM.Massive.Tarn.bearings
#print axioms YM.Massive.Tarn.cant
