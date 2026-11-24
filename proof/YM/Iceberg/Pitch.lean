import YM.Iceberg.Glory
import YM.Iceberg.Hay
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
open Heron Work.A05
variable (A:Persona T V)(J:Axle K (fun a b=>V (a,b))) (U:Vane J) {d:ℕ}(hd:8≤d)(x:Points 2)(hx:x∈conf _)(g:Ortho.Skew)
noncomputable def tapeJ (W:Choir)(S:Axis×Axis→W.W)(J:Axle W (fun a b=>S (a,b)))(hd:8≤d)(g:Ortho.Skew):Module.End ℂ (W.level d):= (J.jet g).restrict (fun i hi=>J.landed d hd g i hi)
noncomputable def wool(k:ℕ)(p:Free.Symbol d) (z:Label d) :ℂ:= K.total 2 ((E.B k).r • x) (![(X.frame k d p).val,cost T E X k z])
noncomputable def steel(k:ℕ): Module.End ℂ (Free.Symbol d) := (X.frame k d).symm.toLinearMap ∘ₗ tapeJ K V J hd g ∘ₗ (X.frame k d).toLinearMap
noncomputable def foldQ(k:ℕ): Module.End ℂ (Free.Symbol d):= (↑(peakΩ V A.tense E X k)⁻¹:ℂ) • steel V E X J hd g k -- order
lemma coat (k:ℕ)(p:Free.Symbol d)(q:Label d): wool E X x k (foldQ V E X A J hd g k p) q=(↑(peakΩ V A.tense E X k)⁻¹:ℂ) * K.total 2 ((E.B k).r • x) (![J.jet g ((X.frame k d p).val),cost T E X k q]):=by
    unfold wool; let v:=X.frame k d; let w:= tapeJ K V J hd g (v p); change K.total 2 _ (Fin.cons (v ((↑(peakΩ V A.tense E X k)⁻¹:ℂ) • v.symm w)).val _) =_; rw [map_smul,v.apply_symm_apply,Submodule.coe_smul,← heads,map_smul,heads]; rfl

variable (R:RawTensor 1 8)(f:ℕ→ℕ)(h:Tendsto f atTop atTop)(hr:∀ i:Face,Tendsto (fun k:ℕ=>(ouzel V E X A (f k)).val i) atTop (𝓝 (R.val i)))
variable (Δ:ℝ→EuPin)(hΔ:EuPin.Path g Δ)(κ:IceT→ℝ)(hκ:symbS 1 R=symbS 1 (bendP (fun i=>(κ i:ℂ))))
variable (s:Hail.RightAuth P.sym)
noncomputable def reachΩ (g:Ortho.Skew)(Δ:ℝ→ EuPin)(hΔ: EuPin.Path g Δ)(κ:IceT→ℝ)(d:ℕ):Module.End ℂ (Free.Symbol d):=∑ i:IceT,(κ i:ℂ) • gran Δ g hΔ i d
noncomputable abbrev scent := points (![0,(1:ℝ) • basis timeAxis])
lemma incomeX (t:Free.Symbol d)(z:Label d) (v:Label d)(hz:projection v=t): UV.Free.wick (fun _:Fin 2=>d) scent (![v,z])= Hail.dual d d scent ((X.base d).liftS t).val z.val:=by
     rw[Hail.wellness]; apply DawnS.trails scent (DawnS.distinct 1 zero_lt_one); intro i; fin_cases i; exact hz.trans ((X.base d).right t).symm; rfl
include hd h hHQ hr hκ hΔ s
include A
private local instance (d:ℕ):Module.Free ℂ (Label d):=Module.Free.of_divisionRing ℂ (Label d)
lemma mist (u:Free.Symbol d) : Tendsto (fun i=> foldQ V E X A J hd g (f i) u) atTop (𝓝 (reachΩ g Δ hΔ κ d u)):=by
     let B:=Module.finBasis ℂ (Label d); let W:= reachΩ g Δ hΔ κ d; let p:=(X.base d).liftS u; let z:= (X.base d).liftS (W u); have hZ:projection p=u:= (X.base d).right _; have hY: projection z=∑ i:IceT, (κ i:ℂ) • gran Δ g hΔ i d (projection p):= by rw [hZ,(show projection z=W u from (X.base d).right _)]; unfold W reachΩ; simp only[LinearMap.sum_apply, LinearMap.smul_apply]
     let Y(q:Label d): Free.Symbol d→ₗ[ℂ]ℂ:= ((Hail.dual d d scent).flip q.val) ∘ₗ (labels d).subtype ∘ₗ (X.base d).liftS
     let F(q:Label d)(k:ℕ): Free.Symbol d →ₗ[ℂ] ℂ:= headG (![cost T E X k q]) ((E.B k).r • scent) ∘ₗ (K.level d).subtype ∘ₗ (X.frame k d).toLinearMap; have he(q:Label d)(k:ℕ)(i: Free.Symbol d):F q k i= wool E X scent k i q:= heads ..
     have hx : scent∈conf 2:= DawnS.distinct 1 zero_lt_one
     apply costW (fun i:Fin _=> F (B i) ∘f) (fun i:Fin _=>Y (B i)) _ _ _ (W u)
     · intro i; let q:= B i; obtain ⟨χ,hχ⟩:= Work.A01.exists_window scent hx; have ht:= breathed hHQ V E X A scent hx g (show Physics.Window scent χ from hχ) p q J f h R hr
       rw[taps Δ g hΔ P.sym s q (fun i=>(κ i:ℂ)) p z hY R hκ scent hx χ hχ,incomeX E X (W u) q z ((X.base d).right _)] at ht -- order
       apply ht.congr'; refine Eventually.of_forall fun i=> Eq.symm ?_ ; dsimp only [Function.comp]; rw [he,coat]; unfold cost; rw [hZ]
     · intro i v; let D:= fun _ : Fin 2=> d; let p:=(X.base d).liftS v; have hp:projection p=v:= (X.base d).right _; have hv := (nourish T E hHQ X _ D (![p,B i]) (Canopy.assay E) (Canopy.reliable hHQ) (Canopy.measureE E) scent hx).comp h
       rw[show UV.Free.wick D scent (![p,B i])=Y (B i) v from incomeX E X v _ _ hp] at hv; apply hv.congr'; apply Eventually.of_forall; intro j; change LoomZ _ _ _ _ _ _ _ _= F (B i) (f j) v; rw[he]; unfold LoomZ wool; apply congr_arg (K.total _ _); funext z; fin_cases z; change cost T E X (f j) p= _; unfold cost; rw[hp]; rfl; rfl
     · intro v hv; let u:=(X.base d).liftS v
       have hL : projection u=0:=by
          apply Hail.shutD P.sym u s; let L:Label d→ₗ[ℂ]ℂ:= Hail.dual d d scent u.val ∘ₗ (labels d).subtype; have h:L=0:= B.ext (fun i=>hv i); intro p; exact DFunLike.congr_fun h p
       exact ((X.base d).right _).symm.trans hL
end YM.Iceberg
#print axioms YM.Iceberg.mist
