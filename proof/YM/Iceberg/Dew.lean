import YM.Iceberg.Lilt
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
-- tested pointwise at moving values
lemma follows_L {W X: Type*}[NormedAddCommGroup W][NormedAddCommGroup X][NormedSpace ℂ W][NormedSpace ℂ X][FiniteDimensional ℂ W](a:ℕ→W→ₗ[ℂ]X)(b: W→ₗ[ℂ] X)(H:∀ w:W,Tendsto (fun i=>a i w) atTop (𝓝 (b w))) (u:ℕ→ W)(v:W)(h:Tendsto u atTop (𝓝 v)): Tendsto (fun i:ℕ=> a i (u i)) atTop (𝓝 (b v)):=by
     let F:= Module.finBasis ℂ W; have he (z:W)(p: W→ₗ[ℂ]X): p z=∑ j,F.coord j z • p (F j):=by simp_rw [←map_smul,←map_sum]; exact congr_arg p (F.sum_repr z).symm
     rw [he v]; have hh : (fun i:ℕ=>a i (u i))=fun i=>∑ j,F.coord j (u i) • a i (F j):=funext fun i=>he ..; rw[hh]; exact tendsto_finsetSum _ (fun j _=> (((F.coord j).continuous_of_finiteDimensional.continuousAt.tendsto.comp h)).smul (H (F j)))
variable {d d' n:ℕ}(i j a:Axis) (p:Label d)(q:Label d')(x:Points 2)(hx:x∈conf 2)
local notation "Ωa"=> (Points.direction (0:Fin 2) a)
noncomputable def veers (k:ℕ):Points 2→ℂ := LoomZ T E K.total (![d,d']) (Hail.petals (A:=Label) p q) X k
lemma hatch (k:ℕ): veers (T:=T) E X p q k x=K.total _ ((E.B k).r • x) (![cost T E X k p,cost T E X k q]):=by
     apply congr_arg (K.total _ _); funext i; fin_cases i<;>rfl
include hHQ hx
open Canopy
lemma furied : Tendsto (fun k=> D Ωa (veers E X p q k) x) atTop (𝓝 (Hail.rayL a x hx d d' p.val q.val)):=by
    let u:= (![d,d']); let v:= Hail.petals (A:=Label) p q; let B:= fun y=> UV.Free.wick u y v
    rw [Hail.D_ray, show (fun z => Hail.dual d d' z p.val q.val)=B from ?_]
    swap; · funext z; rw [Hail.valD]; apply congr_arg (moment _ _); funext i; fin_cases i<;>rfl
    apply Metric.tendsto_nhds.mpr; intro ε hε; let w:= Ωa; let e:=ε/(‖w‖+1); have ht:0<e:=by unfold e; positivity
    filter_upwards [linearW T E hHQ X _ u v (assay E) (reliable hHQ) (measureE E) 1 0 e ht {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)] with k hk; specialize hk _ rfl; rw [pow_zero,one_mul] at hk; rw [dist_eq_norm]; let Z:= veers E X p q k; let M:=iteratedFDeriv ℝ 1 Z x-iteratedFDeriv ℝ 1 B x
    have hh:‖M‖≤e:=hk; let L(i:Fin 1):=w; have hS: ‖M L‖≤ ‖M‖*‖w‖:=by simpa only [Fin.prod_univ_one,L] using! (M.le_opNorm L)
    change ‖D w Z x-D w B x‖ < ε; rw [show (D _ _ _ -D _ _ _)=M L from ?_]; exact (hS.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))).trans_lt (lt_of_lt_of_le (mul_lt_mul_of_pos_left (lt_add_one _) ht) (by unfold e; rw [div_mul_cancel₀ _ (by positivity)])); simp only [M,ContinuousMultilinearMap.sub_apply,iteratedFDeriv_one_apply]; rfl
omit hx hHQ
private lemma brake {V W: Type*}[NormedAddCommGroup V] [NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W](f:V→L[ℝ]W)(x:V): fderiv ℝ (⇑f) x=f:= f.fderiv
noncomputable def bullet (d k:ℕ):Label d→ₗ[ℂ] K.W:= (K.level d).subtype ∘ₗ (X.frame k d).toLinearMap ∘ₗ (@projection d)
noncomputable def daisy (k:ℕ)(x:Points 2)(a:Axis):Label d→ₗ[ℂ]ℂ:= ((E.B k).r:ℂ) • ((headG (![cost T E X k q]) (((E.B k).r:ℝ) • x)) ∘ₗ K.arc a ∘ₗ bullet E X d k)
set_option quotPrecheck false
local notation "κ"=> Compass.vital P φ K
include hx hHQ
lemma lightD (k:ℕ) : D Ωa (veers E X p q k) x=daisy E X q k x a p:=by
     let r:=(E.B k).r; let B:Points 2→L[ℝ] Points 2:= r • ContinuousLinearMap.id ℝ _; let z:=( ![cost T E X k p,cost T E X k q]); let y(x:Points 2):=K.total 2 x z; have hy:veers E X p q k = y ∘ B:=funext fun x=> hatch E X p q x k; rw[hy]
     have ht:B x∈conf 2:= κ hHQ x hx r (E.B k).realH; unfold D; rw [fderiv_comp x (((hHQ.h.smooth 2 z).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt (by simp)) B.differentiableAt,brake B,ContinuousLinearMap.comp_apply]; change fderiv ℝ y _ (r • Ωa)=_; rw[map_smul,show fderiv ℝ y (B x) Ωa =_ from hHQ.h.derivatives 2 _ ht z _ _, show z (0:Fin 2)=cost T E X k p from rfl,show update z _ _= ![K.arc a (cost T E X k p),cost T E X k q] from update0 _ _ _]; change r • K.total _ (B x) _=(r:ℂ) • (headG _ (B x) _ :ℂ); rw [heads]; rfl
lemma lights (L:ℕ→ℕ)(h:Tendsto L atTop atTop) (u:ℕ→ Label d)(hu:Tendsto u atTop (𝓝 p)):Tendsto (fun k=> daisy E X q (L k) x a (u k)) atTop (𝓝 (Hail.rayL a x hx d d' p.val q.val)):=by
    let W:= LinearMap.flip (Hail.rayL a x hx d d') q.val ∘ₗ (labels d).subtype; let Y(k:ℕ):= daisy (d:=d) E X q (L k) x a
    apply follows_L Y W _ _ p hu; intro z; have h0:=furied hHQ E X a z q x hx
    refine (h0.comp h).congr' (Eventually.of_forall fun i=> lightD hHQ E X a z q x hx (L i))
end YM.Iceberg
#print axioms YM.Iceberg.follows_L
#print axioms YM.Iceberg.lights
