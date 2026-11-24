import YM.Rill.Cosmo
/-! Physical cover generation and persistence of payments at independently specified precisions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir} {β e:ℝ} {φ:ℕ→ℕ}(hp:C.Path β e) (H:Q.Harmony P φ) (hφ:Tendsto φ atTop atTop) (G:∀ d,Cottage P d) (hr:Sway C.S)
variable (j i:ℕ)
noncomputable abbrev tagY (Z:E4×Q.W):= Z.1
noncomputable abbrev strand (C:Sequence) (j:ℕ)(x:E4) : Cover:= bead (C.S.spacing (C.N j)) x
abbrev Scan (C:Sequence)(j:ℕ)(x y:E4):Prop:=∃ p:Cover,y=x+digit (C.S.spacing j) p
set_option quotPrecheck false
local notation "Ω" i:arg=> C.S.side (C.R i) (C.N i)
local notation "α" i:arg=> C.S.spacing (C.N i)
lemma structureS {x y:E4} (h: j ≤ C.N i)(he:Scan C j x y): ∃ p:Cover,strand C i y=strand C i x+ratioTo C.S (C.N i) j • p:=by
    obtain ⟨p,rfl⟩:=he; refine ⟨p,funext fun b=>?_⟩; let v:=α i; let A:= ratioTo C.S (C.N i) j; have hκ:v*A=C.S.spacing j:=footprint C.S j _ h
    change ⌊(x b+C.S.spacing j*(p b:ℝ))/(α i)⌋= ⌊x b/(α i)⌋+ A • p b
    have hw:0<α i:=space0 _ _; rw [←hκ,add_div,show v*↑A*↑(p b)/(α i)= (↑(A • p b):ℝ) from (by unfold v; simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; field_simp)]; exact Int.floor_add_intCast ..
include hp
lemma beamV(x y:E4)(j:ℕ) (h:4*C.S.spacing j < dist x y):∀ᶠ i in atTop, ratioTo C.S (C.N i) j < separation (wrap _ (strand C i x)) (wrap (Ω i) (strand C i y)) :=by
     let w:= C.S.spacing j; have hv:= space0 C.S j; have ht:= (approaches hp x).dist (approaches hp y); filter_upwards [ht.eventually_const_le h, ht.eventually_le_const (lt_add_one _), fullPrice hp (4*w) (dist x y+1),hp.uv.tendsto_atTop.eventually_ge_atTop j] with i hi ht hz hI; have hr:= hz _ _ hi ht; let p:= strand C i x; let q:=strand C i y; let u:= separation (wrap _ p) (wrap (Ω i) q); have hD:2*w ≤ (α i)* (u:ℝ):=by rw[show 2*w=4*w/2 from (by ring)]; exact hr
     have ht:C.S.spacing j < (α i)*↑u:= lt_of_lt_of_le (by unfold w; linarith only [hv]) hD; rw [← footprint C.S j _ hI] at ht; exact_mod_cast lt_of_mul_lt_mul_left ht (space0 _ _).le
-- payment for an individual field at resolution j.Limit of W.
abbrev Privilege (P:Calibration C)(Q:Choir)(j:ℕ) (w:Q.W)(p:ℝ):Prop:=∃ d,∃ q:Label d,Q.focus none d q=w∧∀ᶠ i in atTop, GreenP C i j (stem P d i q) p
include H hφ
variable {I J:Type}[Fintype I][Fintype J] (t:I→ E4)(y:J→ E4) (x:Points n)(k:Fin n→ Bool)(v:Fin n→ Q.W)(c:Fin n→ℝ)(j ℓ:ℕ)
set_option maxHeartbeats 390000 in
lemma campuses (hs:j+1 ≤ ℓ)(hK:∀ p, k p=true→ ∃ i:I, Scan C j (t i) (x p)) (hE:∀ p,k p=false→ ∃ i:J,x p=y i) (he:∀ p q,p≠q→ 4*C.S.spacing ℓ < dist (x p) (x q))(hu:∀ p q,p≠q→k p=true→ 4*C.S.spacing j < dist (x p) (x q))(hD:∀ i,Privilege P Q (if k i then j else ℓ) (v i) (c i))(hC:Fintype.card I*8< (C.S.step j).L.val)(hb:Fintype.card J*6 < (C.S.step ℓ).L.val): ‖Q.total n x v‖≤∏ i,c i:=by
     choose d p h hL using hD; let V(i:ℕ)(j:Fin n):=strand C i (x j); have hx:x∈conf n:=by intro i j he'; by_contra h; have hu:= he i j h; rw [he',dist_self] at hu; exact (by linarith only [hu,space0 C.S ℓ] :False)
     have ht:Tendsto (fun i=>pollF C n (φ i) (V (φ i))) atTop (𝓝 x):=by
           let F:= PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin n=>E4); have he: Tendsto (fun i=> F (pollF C n (φ i) (V (φ i)))) atTop (𝓝 (F x)):= tendsto_pi_nhds.mpr fun j=> (approaches hp (x j)).comp hφ; have hv:=(F.symm.continuous.tendsto _).comp he; rw [F.symm_apply_apply] at hv; exact hv
     have hw:= H.picks d (fun _=>none) p x hx ht; rw [← funext h]; apply le_of_tendsto hw.norm
     have hQ: ∀ᶠ i in atTop, ‖Fields.Limit.evaluation C P d p (fun _=>none) (V i) i‖≤ ∏ i,c i:=by
          let X:= {p:Fin n × Fin n // p.1≠p.2}; let Y:= {q:X// k q.val.1=true}; filter_upwards [eventually_all.mpr hL, eventually_all.mpr (fun i:X=> beamV hp (x i.val.1) (x i.val.2) ℓ (he _ _ i.property)), eventually_all.mpr (fun i:Y=>beamV hp (x i.val.val.1) (x i.val.val.2) j (hu _ _ i.val.property i.property)),hp.uv.tendsto_atTop.eventually_ge_atTop (ℓ+1)] with i hI hv hU ht
          refine twin hp i j ℓ hs ht (strand C i ∘ t) (strand C i ∘ y) (V i) (fun k=> stem P (d k) i (p k)) c k hC hb ?_ ?_ (fun i j he=> hv ⟨(i,j),he⟩) (fun i j he hr=>hU ⟨⟨(i,j),he⟩,hr⟩) ?_ ?_
          · intro a hx; obtain ⟨u,hz⟩:=hK a hx; exact ⟨u,structureS _ _ (by omega) hz⟩
          · intro z hx; obtain ⟨u,h⟩:=hE z hx; exact ⟨u,congr_arg (strand C i) h⟩
          · intro z hx; specialize hI z; simpa only[hx,↓reduceIte] using hI
          intro z hx; specialize hI z; simpa only[hx,Bool.false_eq_true,↓reduceIte] using hI
     exact hφ.eventually hQ
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.campuses
