import YM.Elix.Jamb
import YM.Elix.Noise
import YM.Avian.Wards
/-! ΑRC QUEST: paid on same order-mix.
    probe only one entry from rank-three family.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx.Gourd
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper SourceRead Oriole Patria.Rolls Tawny Cast Carnal
open YM.MassiveMasses.FreePair Tarn Tarn.Choir Tarn.Choir.Measures YM.Analysis
open YM.Intag.Sprig YM.Intag.Sprig.Canopy YM.Sprig YM.Sprig.Lanterns -- ambiguity
open scoped Topology
variable {C:Sequence}{P:Calibration C}{Q:Choir}{φ:ℕ→ℕ}(hD:Q.Domestic)(T: Pollens P Q)(E:Canopy P φ Q)
variable (J:Lanterns T E)(hQ:Q.Harmony P φ)
local notation "X"=> basis 2
local notation "U"=> (fun i:Fin 2=>6)
local notation "Α"=> Measures.arm
local notation "Ω"=> Α X
local notation "Ψ"=> Α
local notation "F"=> Flavor 6
-- Αrthur scaler
variable (a b:F)(i:Axis)
noncomputable def beamA(i:ℕ)(a b:Flavor 6)(j:Axis):= LoomZ T E Q.total (fun _ : Fin 2 =>6) (![gamma6 a 2 0 1, gamma6 b j 0 1]) J i
include hQ
omit hQ
private lemma chain {V W: Type*}[NormedAddCommGroup V] [NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W](f:V→L[ℝ]W)(x:V): fderiv ℝ (⇑f) x=f:= f.fderiv
include hQ
set_option maxHeartbeats 650000 in
lemma feral : Tendsto (fun k=> D (Α (basis i)) (beamA T E J k a b i) Ω ) atTop (𝓝 (D (basis i) (s1 a b i) X)):=by
     let δ:= basis i; let u (i:Fin 2):=6; let p:=(![gamma6 a 2 0 1,gamma6 b i 0 1]:(i:Fin 2)→Label (u i)); let B(x:Points 2):= UV.Free.wick u x p; let G(k):= beamA T E J k a b i
     have he:X≠0:=by intro h; have ht:= basis_norm 2; rw[h,norm_zero] at ht; exact zero_ne_one ht
     have hΩ:Ω∈conf 2:=Measures.forms he
     have hp:D δ (s1 a b i) X=D (Α δ) B Ω:=by
          have hv:ContDiffAt ℝ ⊤ B Ω:= UV.Free.Sip.smoothC hΩ u (fun i=>(p i).val)
          unfold D; change fderiv ℝ (B ∘ Α) X _=_; rw[fderiv_comp X (hv.differentiableAt (by simp)) Measures.arm.differentiableAt,chain Measures.arm X,ContinuousLinearMap.comp_apply] -- syntax Top infinity
     rw [show D _ _ _ =_ from hp]; apply Metric.tendsto_nhds.mpr; intro ε hε; let v:= Α δ; let e:= ε/(‖v‖+1); have ht:0<e:=by unfold e; positivity
     filter_upwards [linearW T E hQ J _ u p (assay E) (reliable hQ) (measureE E) 1 0 e ht {Ω} isCompact_singleton (Set.singleton_subset_iff.mpr hΩ)] with k hk; specialize hk _ rfl; rw [pow_zero,one_mul] at hk; rw [dist_eq_norm]; let M:=iteratedFDeriv ℝ 1 (G k) Ω-iteratedFDeriv ℝ 1 B Ω
     have hh: ‖M‖≤e:= hk; let L(i:Fin 1):=v; have hf: ‖M L‖≤ ‖M‖*‖v‖:=by simpa only [Fin.prod_univ_one,L] using (M.le_opNorm L)
     
     change ‖D v (G k) Ω-D v B Ω‖ < ε; rw [show (D _ _ _ -D _ _ _)=M L from ?_]; exact (hf.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))).trans_lt (lt_of_lt_of_le (mul_lt_mul_of_pos_left (lt_add_one _) ht) (by unfold e; rw [div_mul_cancel₀ _ (by positivity)])); simp only [M,ContinuousMultilinearMap.sub_apply,iteratedFDeriv_one_apply]; rfl
set_option maxHeartbeats 750000 in
lemma derivands (k:ℕ)(x:E4)(hx:x≠0): D (Α (basis i)) (beamA T E J k a b i) (Α x)= (E.B k).r • ans2 (cost T E J k (gamma6 a 2 0 1)) (Q.arc i (cost T E J k (gamma6 b i 0 1))) ((E.B k).r • x):=by
     let r:=(E.B k).r; let Z:Points 2→L[ℝ] Points 2:= r • ContinuousLinearMap.id ℝ _
     let v':= cost T E J k (gamma6 a 2 0 1); let w':= cost T E J k (gamma6 b i 0 1); let y(x:Points 2):= Q.total 2 x ![v',w']; have hz: beamA T E J k a b i=y∘ Z:=by
          funext x; apply congr_arg (Q.total 2 (r • x)); funext i; fin_cases i<;>rfl
     rw[hz]; have hc:Α x∈ conf 2:=forms hx; have ht:Z (Α x)∈conf 2:= Compass.vital P φ Q hQ _ hc r (E.B k).realH
     have hy:D (Α (basis i)) y (Z (Α x))= ans2 v' (Q.arc i w') (r • x):=by
          rw [axis_l]; unfold y; rw[hQ.h.derivatives 2 (Z (Α x)) ht]; have hv:update ![v',w'] 1 (Q.arc i (![v',w'] (1:Fin 2)))=![v',Q.arc i w']:=by funext i; fin_cases i<;>simp -- binder capture macro
          rw [hv]; change Q.total _ (r • (Α x)) _ = Q.total _ (Α _) _; rw [map_smul]
     unfold D; rw [fderiv_comp (Α x) (((hQ.h.smooth 2 ![v',w']).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt (by simp)) Z.differentiableAt,chain Z,ContinuousLinearMap.comp_apply]; change fderiv ℝ y _ (r • (Α _))=_; rw [map_smul]; exact congr_arg (r • ·) hy
-- columns
noncomputable def moon (k:ℕ): Matrix (Flavor 6) (Flavor 6) ℂ:= fun a b=> ∑ i:Axis,D (Α (basis i)) (beamA T E J k a b i) Ω
local notation "κ"=> (((↑(2*Maxwell.normal)):ℂ))
local notation "Lk"=> ((48:ℂ)* κ^2) • (1:Matrix (Flavor 6) (Flavor 6) ℂ)
lemma major : ∃ k:ℕ, IsUnit (moon T E J k):=by
     have hK:Tendsto (moon T E J) atTop (𝓝 (Lk)):=by
          apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
          change Tendsto (fun k=> ∑ z:Axis,_) atTop (𝓝 (_:ℂ)); convert! (tendsto_finsetSum (s:=@Finset.univ Axis _) (fun z _=> feral T E J hQ i j z)) using 1
          rw [sigmaW]; simp_rw [Matrix.smul_apply,Matrix.one_apply]; split <;>simp
     have hp: κ≠0:= Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Maxwell.normal_pos).ne'; have hl:(Lk).det≠0:=by simp [Maxwell.normal_pos.ne']
     have h':∀ᶠ i in atTop,(moon T E J i).det≠0:= ((((show Continuous (fun i:Matrix (Flavor 6) (Flavor 6) ℂ=>i.det) from Continuous.matrix_det (A:=fun i:Matrix (Flavor 6) (Flavor 6) ℂ=>i) continuous_id)).continuousAt (x:=Lk)).tendsto.comp hK).eventually (isOpen_ne_fun continuous_id continuous_const|>.mem_nhds (x:=(Lk).det) hl) -- name
     obtain ⟨k,hk⟩:=h'.exists; exact ⟨k,(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hk)⟩
end YM.Massive.Patria.Gall.Onyx.Gourd
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.feral
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.major
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.derivands
