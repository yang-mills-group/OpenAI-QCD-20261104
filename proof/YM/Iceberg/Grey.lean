import YM.Iceberg.Dew
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
variable (V:Face→K.W)(hv:Tense T V)(E:Canopy P φ K) (X:Lanterns T E)
open Lanterns Tawny Tawny.Cast Perla Carnal Drill
local notation "Rx" => RawTensor 1 8
variable (A:Persona T V)
noncomputable def mintS (k:ℕ):ℝ:= (peakΩ V A.tense E X k)⁻¹ * (E.B k).r^4
noncomputable def ouzel(k:ℕ):Rx:= (mintS V E X A k:ℂ) • patrolS V A.tense E X k
lemma spy (k:ℕ)(i:Face): projection ((ouzel V E X A k).val i)=aceG V E X k A.tense i:=by
     unfold ouzel mintS; rw [Submodule.coe_smul, Pi.smul_apply,map_smul,petrol]; unfold aceG paceG; rw[Pi.smul_apply,Pi.smul_apply,smul_smul]; push_cast; rfl
lemma spyR (k:ℕ)(i:Face): bullet E X 8 k ((ouzel V E X A k).val i)= (mintS V E X A k:ℂ) • V i:=by
     unfold ouzel; rw[Submodule.coe_smul, Pi.smul_apply,map_smul]; apply congr_arg; change (X.frame k 8 (projection ((patrolS V A.tense E X k).val i))).val=_; rw[petrol,airs,(X.frame k 8).apply_symm_apply]; rfl
lemma pearS(k:ℕ)(i:Face): ((ouzel V E X A k).val i)=(X.base 8).liftS (projection ((ouzel V E X A k).val i)):=by unfold ouzel; rw[Submodule.coe_smul, Pi.smul_apply,patio,map_smul,(X.base 8).right,map_smul]
variable (f:ℕ→ℕ)(hF:Tendsto f atTop atTop)
set_option quotPrecheck false
local notation "F" i:arg=> ouzel V E X A (f i)
variable (U:Face→Free.Symbol 8)(hU:Tendsto (fun i=> aceG V E X (f i) A.tense) atTop (𝓝 U))
include hU A
lemma yarn:∃ R:Rx,(symbS 1 R)=U ∧ ∀ i:Face,Tendsto (fun k:ℕ=>(F k).val i) atTop (𝓝 (R.val i)):=by
     let Q(i:Face):= (X.base 8).liftS (U i); have h(i:Face):Tendsto (fun k:ℕ=>(F k).val i) atTop (𝓝 (Q i)):=by
                apply (((X.base 8).liftS.continuous_of_finiteDimensional.continuousAt (x:=U i)).tendsto.comp (tendsto_pi_nhds.mp hU i)).congr' (Eventually.of_forall fun k=>by change (X.base 8).liftS (aceG V E X (f k) A.tense i)=_; rw [← spy V E X A (f k) i]; exact (pearS V E X A _ i).symm)
     have hh : Q∈ Rx:=(show IsClosed (Rx : Set (Axis×Axis → Label 8)) from (Rx).closed_of_finiteDimensional).mem_of_tendsto (show Tendsto (fun k:ℕ=>(F k).val) atTop (𝓝 Q) from tendsto_pi_nhds.mpr h) (Eventually.of_forall fun i=>(F i).property)
     exact ⟨⟨Q,hh⟩, funext fun i=>(X.base 8).right _, h⟩

omit hU
variable (R:RawTensor 1 8)
include hF hHQ
open Finset
lemma bankV (hR:∀ i:Face,Tendsto (fun k:ℕ=>(ouzel V E X A (f k)).val i) atTop (𝓝 (R.val i))) (x:Points 2)(hx:x∈ conf 2)(a:Axis)(p:Label 10): Hail.gale x hx R a p.val=0:=by
     let B(j:ℕ)(i:Axis):= daisy E X p (f j) x i ((F j).val (i,a)); have h(i:Axis):Tendsto (fun j=>B j i) atTop (𝓝 (Hail.rayL i x hx 8 10 (R.val (i,a)).val p.val)):=lights hHQ E X i (R.val (i,a)) p x hx f hF (fun k=>(ouzel V E X A (f k)).val (i,a)) (hR (i,a))
     unfold Hail.gale; rw[LinearMap.sum_apply]; refine tendsto_nhds_unique (tendsto_finsetSum Finset.univ (f:=fun i j=>B j i) (fun i _=>h i)) ?_
     apply tendsto_const_nhds.congr' (Eventually.of_forall fun j=>?_)
     let r:=(E.B (f j)).r; let w:=cost T E X (f j) p; let c:ℂ:=mintS V E X A (f j); have hv:(∑ i:Axis,K.arc i (V (i,a)))=0:= by have h:=congr_fun A.div a; rw[divR,LinearMap.pi_apply,LinearMap.sum_apply] at h; exact h
     change 0= ∑ i:Axis, (r:ℂ) • headG (![w]) _ (K.arc i _); simp_rw [show ∀ i:Axis,bullet E X 8 (f j) ((F j).val (i,a))= c • V (i,a) from (fun i=>spyR V E X A ..),map_smul,← Finset.smul_sum,← map_sum, hv,map_zero,smul_zero] -- synt?
lemma stand (hR:∀ i:Face,Tendsto (fun k:ℕ=>(ouzel V E X A (f k)).val i) atTop (𝓝 (R.val i))) (i:Face)(hy: onceF K (V i)=0): Hail.crossH 0 R i=0:=by
     let v:Fin 1→ℕ:=fun _=>8
     let Z:Label 8→ₗ[ℂ]ℂ:= ((moment v 0).toLinearMap 0 0) ∘ₗ (labels 8).subtype
     have h0:(0:Points 1)∈conf 1:=fun _ _ _=>Subsingleton.elim ..
     let q(k:ℕ):= onceF K ∘ₗ bullet E X 8 (f k)
     have h(p:Label 8): Tendsto (fun k=> q k p) atTop (𝓝 (Z p)):=by
          let U(j:Fin 1):Label (v j):= p; have hx:= (nourish T E hHQ X _ v U (Canopy.assay E) (Canopy.reliable hHQ) (Canopy.measureE E) _ h0).comp hF
          rw[show Z p=UV.Free.wick v 0 U from Hail.monoV (0:Points 1) h0 p.val]; apply hx.congr'; apply Eventually.of_forall; intro i; change LoomZ T E _ v U X _ _= onceF K (bullet E X 8 (f i) p); unfold LoomZ; rw [smul_zero,←mint]; apply congr_arg; funext j; fin_cases j; rfl
     rw [show Hail.crossH _ _ _=Z (R.val i) from (Hail.monoV _ h0 _).symm]
     apply tendsto_nhds_unique (follows_L q Z h _ _ (hR i)); apply tendsto_const_nhds.congr'; apply Eventually.of_forall; intro j; change 0= onceF K (bullet E X 8 (f j) _); rw [spyR,map_smul,hy,smul_zero]
end YM.Iceberg
#print axioms YM.Iceberg.yarn
#print axioms YM.Iceberg.bankV
#print axioms YM.Iceberg.stand
