import YM.Shade.Aster
/-! The authentic iso metering row connected to continuum rank. -/
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
variable {d:ℕ}(w:Label d)(r:Averaging)(v:Label d)(z y:ℕ→Label d)(hv:Tendsto (y∘φ) atTop (𝓝 v))(hx:Tendsto (z∘φ) atTop (𝓝 w)) (A:Set E4)(x:E4)(ℓ:ℕ)(b:Cover)
local notation "Ω" i:arg=> C.S.side (C.R i) (C.N i)
noncomputable def tapW (P:Calibration C)(ℓ i:ℕ)(b:Cover)(r:Averaging)(a:Label d):Label d→ₗ[ℂ]ℂ where
    toFun p:= rod2 C i (stem P d i a) (checkedT r (ratioTo C.S (C.N i) ℓ) (stemV P d i r p) b)
    map_add' x y:=by rw [map_add,tickM,map_add]; -- hygiene
    map_smul' t p:=by rw[map_smul,chimes]; unfold rod2; change button _ _ _ _ _=_; unfold button; rw [mul_smul_comm,map_smul]; rfl
abbrev Pasture (C:Sequence)(ℓ:ℕ)(b:Cover)(A:Set E4):Prop:=∀ᶠ i:ℕ in atTop,∀ z∈Lattice.box (flex C.S ℓ (C.N i)),digit (C.S.spacing (C.N i)) (ratioTo C.S (C.N i) ℓ • b+z)∈A
include hx hv H hp hφ
local notation "T" i:arg=> tapW P ℓ i b r
lemma nullS (he:Q.focus r d v=0) (hN:IsCompact A)(hA:0∉A)(hb:Pasture C ℓ b A): Tendsto (fun i=>tapW P ℓ (φ i) b r (z (φ i)) (y (φ i))) atTop (𝓝 0):=by
     let D:Fin 2→ℕ:=fun _=>d; let G:Fin 2→ Averaging:=![none,r]; let Y:=(fun i=> ![z (φ i),y (φ i)]); let B:=![w,v]; let F := eyeW P D G
     let V(t:Points 2):ℂ:= Q.total 2 t (fun j=>Q.focus (G j) d (B j))
     have hy:Tendsto Y atTop (𝓝 B):=tendsto_pi_nhds.mpr fun i=> by fin_cases i; exact hx; exact hv
     let K:= arm '' A; have ht:K⊆ conf 2:=by rintro _ ⟨x,h,rfl⟩; exact forms (fun he=>hA (he ▸ h))
     refine Metric.tendsto_nhds.mpr fun ε hE=>?_
     have hc:= compactity K (hN.image arm.continuous) (show ContinuousOn V K from ((H.h.smooth _ _).continuousOn.mono ht)) (fun x hp=> H.exposed D G B Y hy x (ht hp)) (ε/2) (half_pos hE)
     filter_upwards [hc, hφ.eventually hb,(hp.uv.tendsto_atTop.comp hφ).eventually_ge_atTop ℓ] with i hi hM hP; let j:=φ i; let f:= z j; let Z:=stemV P d j r (y j); let W:= rod2 C j (stem P d j f)
     have hh(p:Cover): eyeW P D G j ![0,p] (Y i)= W (Z p):=by change (C.A j).regulator.average (List.ofFn (fun t:Fin 2=> stemV P (D t) j (G t) (Y i t) ((![0,p] :Fin 2→ Cover) t))).prod= _; simp only[List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; rfl
     have hX(x:Points 2):V x=0:=(Q.total 2 x).map_coord_zero (1:Fin 2) (show Q.focus (G 1) _ (B 1)=0 from he) -- order
     let V':=ratioTo C.S (C.N j) ℓ; obtain ⟨g,hg,hF,hK⟩:= strummed C.S b r Z (show ℓ≤ C.N j from hP); change dist (W (Averaging.filter r (ratioTo C.S (C.N j) ℓ) Z (ratioTo C.S (C.N j) ℓ • b))) 0 < ε; rw [dist_eq_norm,hK,map_sum]; simp_rw [map_smul]; apply lt_of_le_of_lt (?_: _ ≤ ε/2) (half_lt_self hE)
     refine purseL _ _ _ 0 hg hF fun a=>?_; let p:= V' • b+a.val; have hQp:=hi (![0,p]) ⟨_, hM a.val a.property,(yards _ _).symm⟩; rw[dist_eq_norm] at hQp; change ‖eyeW P D G j ![0,p] (Y i)-V _‖≤ _ at hQp; rw [hh,hX] at hQp; exact hQp
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.nullS
