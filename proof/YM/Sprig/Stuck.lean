import YM.Sprig.Peri
/-! Recover rescaled field basis parameters before assuming proper rotations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
variable {C:Sequence} {D d n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
namespace Compass
variable (A:Compass C D)
variable (φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
variable (K:DiscP P A φ V Q) (L:Vale.Laurel d)(J:Vale.Landing P.sym L)
structure Inn (A:Compass C D) {L: Laurel d}(J: Landing P.sym L): Prop where
    level:d ≤ D
    rich : ∀ i: Stokes d, GlyphV (L.F i) D level ∈ A.Ω ∧ GlyphV (opposite P.sym timeAxis (L.F i)) D level∈ A.Ω
    suit : A.e ≤ J.e
    vast : J.v≤ A.v
    poise: A.bid≤ J.ε/4
variable (B:Inn P A J)
noncomputable abbrev glimpseT (f g: Q.W)(y:E4):= Q.total 2 (A.r • (points ![0,y])) (![f,g])
noncomputable abbrev fieldS(i:Stokes d):= choiceT V Q (L.F i).mark
noncomputable abbrev oppositeX(i:Stokes d):= choiceT V Q (opposite P.sym timeAxis (L.F i)).mark
local notation "S"=>Q.total
-- Gram encoder arbitrary second f
local notation "Z"=> Stokes d
local notation "W"=> (oppositeX P V Q L)
local notation "Tq"=> (fieldS V Q L)
noncomputable def curveP (y:E4)(i j: Stokes d):= glimpseT A Q (oppositeX P V Q L i) (fieldS V Q L j) y
local notation "G"=> curveP P A V Q L
include B
include K
open Metric
lemma mediator(y:E4)(h:y∈ball J.a J.l): nearG P.sym L J.ε (curveP P A V Q L y):=by
     let f:=L.F
     let d₀:= B.level
     let U i:=GlyphV (L.F i) D d₀; let m i:=GlyphV (opposite P.sym timeAxis (L.F i)) D d₀
     intro i j; let T:=berth P.sym L d₀ i j
     have he:ΦGram P.sym L y i j=candle T (![0,y]):= (berth_g ..).symm
     have hp(q:Fin 2): T q∈ A.Ω:=by fin_cases q; exact (B.rich i).2; exact (B.rich j).1
     have hh(q:Fin 2): (T q).material≠0:=by fin_cases q; exact (fun h=> living L i ((P.sym.adj d timeAxis).injective (h.trans (map_zero _).symm))); exact living L j
     have hk(y:E4) : learned A V Q T (![0,y])=G y i j:=by
              unfold curveP glimpseT learned; apply congr_arg (S 2 _); funext k; fin_cases k<;>rfl
     have hu: ‖G y i j-ΦGram P.sym L y i j‖ ≤ J.ε/4:= by rw [he,←hk]; exact (K.homes T hp hh d L J B.suit B.vast y h).trans B.poise
     have hx := ((J.pose y (ball_subset_closedBall h)).2.2 i j).le; exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hu hx).trans (by linarith only [J.light]))
noncomputable def harp : (Stokes d→ℂ)→ₗ[ℂ] ↥(Q.level d) where
    toFun x:= ⟨∑ i:Stokes d,x i • fieldS V Q L i, Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (⟨_,rfl⟩: (fieldS V Q L i) ∈ Q.level d)⟩
    map_add' x y:= Subtype.ext (by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; rfl)
    map_smul' c x:= Subtype.ext (by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; change ∑ i:Stokes d,(c*x i)• Tq i=c • ∑ i,x i • Tq i; rw [Finset.smul_sum]; simp [mul_smul])
omit K B
noncomputable def tap (x:Q.W)(y:E4):Q.W→ₗ[ℂ]ℂ:= (Q.total 2 (A.r • (points ![0,y]))).toLinearMap (![x,0]) 1
lemma pours (x:Q.W)(y:E4)(z:Q.W):tap A Q x y z= glimpseT A Q x z y:=congr_arg (S 2 _) (funext fun i=>by fin_cases i <;> simp)
lemma stringed (r: Stokes d →ℂ)(x:E4)(j:Stokes d) : Γ (curveP P A V Q L x) r j=tap A Q (W j) x (harp V Q L r):=by
     change ∑ i:Z,G x j i*r i=tap A Q (W j) x (∑ i,r i • Tq i); rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,pours]; exact mul_comm ..
include K B
lemma keyH : Injective (harp V Q L):=by
      intro x y h; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp
      have hv: (harp V Q L) (x-y)=0:= (map_sub ..).trans (sub_eq_zero.mpr h); let f:=G J.a; have hh:Γ f (x-y)=0:=by
           funext i; unfold f; rw[stringed,hv]; exact map_zero _
      exact (J.warmth (mediator P A φ V Q K L J B J.a (Metric.mem_ball_self J.breadth)) (x-y)).trans (by rw [hh,norm_zero,mul_zero])
include hQ
lemma tableH : Bijective (harp V Q L):= ⟨keyH P A φ V Q K L J B, ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (show Module.finrank ℂ (Stokes d→ℂ) = Module.finrank ℂ (Q.level d) from (by rw [hQ.h.faith]; simp [Module.finrank_pi, Stokes]))).1 (keyH P A φ V Q K L J B))⟩
noncomputable abbrev coil : (Stokes d→ℂ)≃ₗ[ℂ] ↥(Q.level d):=LinearEquiv.ofBijective (harp V Q L) (tableH P A φ V Q hQ K L J B)
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.coil
