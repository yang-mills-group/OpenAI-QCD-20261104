import YM.Sunda.Cup
import YM.Kauri.Apex
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
local notation "Ω"=> Free.Symbol
variable (d:ℕ)
structure Glace (A:Axle K (fun a b=>W (a,b)))(I:ℕ→ℕ)(X:Lanterns T E)(R:Roof P.sym)(ρ:EuPin →* (K.W ≃ₗ[ℂ] K.W))(F:∀ d:ℕ,ℕ→ Ω d≃ₗ[ℂ] ↥(K.level d)): Prop where
    prose d i: Prose (F d i) T
    lifts d (x: Label d) i p : (F d i (projection (P.sym.pin d p x))).val= ρ p (F d i (projection x)).val
    smooth d (x:Ω d): Tendsto (fun i=> (X.frame (I i) d).symm (F d i x)) atTop (𝓝 x)
include J H JQ B R S
lemma glossed : ∃ F:∀ d:ℕ,ℕ→Ω d≃ₗ[ℂ] ↥(K.level d), Glace A I X R ρ F:=by
      have hv (d:ℕ):∃ F:ℕ→ Ω d≃ₗ[ℂ] ↥(K.level d),(∀ i,Prose (F i) T)∧(∀ (x:Label d) i p,(F i (projection (P.sym.pin d p x))).val= ρ p (F i (projection x)).val)∧∀ x:Ω d,Tendsto (fun i=> (X.frame (I i) d).symm (F i x)) atTop (𝓝 x):=by
           by_cases h:d<8
           · refine ⟨fun i=>X.frame (I i) d, fun i=> X.leaders _ _,fun x i p=>(kisses J H JQ B R S h (X.frame (I i) d) (X.leaders _ _) x p).symm,fun x=>?_⟩; simp
           obtain ⟨F,hF,hv⟩:= mints J H JQ B R (le_of_not_gt h); exact ⟨F,fun i=>(hF i).toProse,fun x i p=>by rw [S.tones _ _ (F i) (hF i), clanP],hv⟩
      choose F hf ht he using hv; exact ⟨F,hf,ht,he⟩
omit J H JQ B R S
lemma haleP {V:Type}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V] (F:ℕ→ V≃ₗ[ℂ] V)(h:∀ v:V,Tendsto (fun i=>F i v) atTop (𝓝 v))(w:ℕ→ V)(v:V)(hv:Tendsto w atTop (𝓝 v)) : Tendsto (fun i=>(F i).symm (w i)) atTop (𝓝 v):=by
      haveI:CompleteSpace V:=FiniteDimensional.complete ℂ V; let A:= Module.finBasis ℂ V
      let L(i:ℕ):V→L[ℂ] V:= (F i).toContinuousLinearEquiv.toContinuousLinearMap; let P(i:ℕ):V →L[ℂ] V:= (F i).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hh(b: V→L[ℂ] V) : b = ∑ j,(A.coord j).toContinuousLinearMap.smulRight (b (A j)):=by
              ext1 x; rw [ContinuousLinearMap.sum_apply]; exact (congr_arg b (A.sum_repr x).symm).trans (by rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; rfl)
      have hL:Tendsto L atTop (𝓝 1):=by
              have ht:= (show Tendsto (fun i:ℕ=> ∑ j,(A.coord j).toContinuousLinearMap.smulRight (L i (A j))) atTop (𝓝 (∑ j,(A.coord j).toContinuousLinearMap.smulRight ((1:V→L[ℂ] V) (A j)))) from ?_); rw [← hh] at ht; exact ht.congr' (Eventually.of_forall fun x=> (hh _).symm)
              apply tendsto_finsetSum; intro j _; exact ((ContinuousLinearMap.smulRightL ℂ V V ((A.coord j).toContinuousLinearMap)).continuous.continuousAt.tendsto.comp (show Tendsto (fun i=> L i (A j)) atTop (𝓝 ((1:V→L[ℂ]V) (A j))) from h (A j))) -- args
      let Q(i:ℕ): (V→L[ℂ] V)ˣ:= ⟨L i,P i, ContinuousLinearMap.ext ((F i).apply_symm_apply),ContinuousLinearMap.ext ((F i).symm_apply_apply)⟩; have hp:= (NormedRing.inverse_continuousAt (1:(V→L[ℂ] V)ˣ)).tendsto.comp hL -- Tendsto syntax
      have hP:Tendsto P atTop (𝓝 1):=by
             change Tendsto _ _ (𝓝 (Ring.inverse (1:V→L[ℂ] V))) at hp; rw [Ring.inverse_one] at hp; apply hp.congr'; refine Eventually.of_forall fun i=>?_ ; change Ring.inverse (Q i).val=(↑((Q i)⁻¹)); exact Ring.inverse_unit _
      exact (show Continuous fun x:(V→L[ℂ]V) × V=>x.1 x.2 from by fun_prop).continuousAt.tendsto.comp (hP.prodMk_nhds hv)
open Kauri
include J
variable (F:∀ d:ℕ,ℕ→ Ω d ≃ₗ[ℂ] ↥(K.level d))(hG:Glace A I X R ρ F)
include hG R
noncomputable def hops (T: Pollens P K) (A:Axle K (fun a b=>W (a,b)))(E:Canopy P φ K)(I:ℕ→ℕ)(ρ:EuPin→* (K.W≃ₗ[ℂ]K.W))(F:∀ d:ℕ,ℕ→ Ω d≃ₗ[ℂ] ↥(K.level d)): Bases (equip T ρ A.jet):=⟨fun i=>(E.B (I i)).r,fun i d=>F d i⟩
local notation "Δ"=> hops T A E I ρ F
variable (i j:Axis)
lemma dueN : ∃ (t:Label 8) (h:W (i,j)∈ (K.level 8)),t.val= UV.totalStress i j∧ Tendsto ((hops T A E I ρ F).stressAt (W (i,j)) h) atTop (𝓝 (-(hops T A E I ρ F).choice 0 t)):=by
      let v:=TTot.val (i,j); refine ⟨-v,J.n.tense.lv _, (show (-v).val=totalStress i j by change -(TTot.val _).val= _; rw [show (TTot.val (i,j)).val= _ from magic i j,neg_neg]),?_⟩ -- magic signature
      let sℓ (k:ℕ):= (↑(((E.B (I k)).r)^4):ℂ) • (⟨W (i,j),J.n.tense.lv _⟩:K.level 8); have hQ:Tendsto (fun k=>(X.frame (I k) 8).symm (sℓ k)) atTop (𝓝 (projection v)):=by
             have ht:= psalm J (pulseB (i,j)); rw[ele] at ht; apply ht.congr'; refine Eventually.of_forall fun k=>?_ ; dsimp only; unfold suitT; rw [LinearMap.smul_apply,LinearMap.comp_apply, LinearEquiv.coe_coe,show employ J (pulseB (i,j))= ⟨W (i,j),J.n.tense.lv _⟩ from pulseB.toBasis.constr_basis _ _ _]; unfold sℓ; rw [map_smul,Complex.ofReal_pow]
      let L(k:ℕ):Ω 8≃ₗ[ℂ] Ω 8:= (F 8 k).trans (X.frame (I k) 8).symm; have hm:Tendsto (fun k=> (F 8 k).symm (sℓ k)) atTop (𝓝 (projection v)):=by
             apply (haleP L (hG.smooth 8) _ (projection v) hQ).congr'; refine Eventually.of_forall fun i=>?_ ; change (F 8 i).symm (X.frame _ _ ((X.frame (I i) 8).symm _))= _; rw [LinearEquiv.apply_symm_apply]
      let Y:= (K.level 8).subtype ∘ₗ (F 8 0).toLinearMap; have he:=Y.continuous_of_finiteDimensional.continuousAt.tendsto.comp hm; rw [show -(hops T A E I ρ F).choice 0 (-v)= Y (projection v) from ?_]; exact he
      change - Y (projection (-v))=_; rw [show projection (-v)= _ from map_neg projection v,map_neg,neg_neg]
end YM.Mako
#print axioms YM.Mako.glossed
#print axioms YM.Mako.dueN
