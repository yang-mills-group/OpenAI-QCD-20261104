import YM.Sprig.DialP
/-! Whole symbol pre-spacetime comparison (all raw; figures pinned). -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF Massive.Elm.SparK.Arbor.PlaneG
variable (φ:ℕ→ℕ)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
open Function Set Finset Metric Compass
namespace Canopy
open _root_.YM.Sprig.Video
variable {P φ Q}(E:Canopy P φ Q)(S:KForm Q)(s:Groom Q S)(H:Money E S)(hv:Troupe E S)
lemma measureE: Troupe E Q.total:=by
    constructor; intro n x hx K hk hK q ε he; filter_upwards [E.care K hk hK 2 (1/2) (by norm_num) (by norm_num), E.many.eventually_ge_atTop n, (E.shots q).eventually_le_const he, E.copperP x hx] with i hp hw hz h
    intro A f y hs; obtain ⟨F,ht⟩:=h; let X(j:Fin n):= GlyphV (x j).2 _ (F j); have hT(j:Fin n): (X j).material≠0:= (hx j).1
    have hh:= hp hs; let l:=E.B i; have hu:l.qR l.ℓ ∘ f∈flats (Fin n) (2*l.e) (l.v/2):=by rw[show l.v/2= (1/2)*l.v from (by ring)]; exact hh
    have h:= (E.checkedW i).book n X ht hT hw f hu
    have he : E.errorP Q.total x i y= learned l (E.V i) Q X y.ofLp-candle X y.ofLp:= rfl
    rw [he]; exact (mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans (E.charge i)) _)).trans hz
lemma assay: Money E Q.total:=⟨fun n t hx K hk hv=>⟨n,1,zero_le_one,(E.sequels t hx K hk hv).mono fun i hi y hy=> le_trans (hi y hy) ((one_mul _).symm.le)⟩⟩
include hQ
lemma reliable: Groom Q Q.total:=⟨hQ.h.smooth,fun n v y hy p a=> hQ.h.derivatives _ y hy v p a⟩
variable (T:Fin n→ℕ)(p:(i:Fin n)→ Label (T i))
noncomputable def rCorr(k:ℕ)(y:Points n):MultilinearMap ℂ (fun i:Fin n=>Label (T i)) ℂ := (S n ((E.B k).r • y)).compLinearMap (fun i=> (Q.focus none (T i)).comp (E.V k (T i)))
noncomputable def pErr(k:ℕ)(y:Points n):= (rCorr E S T k y-UV.Free.wick T y) p
noncomputable def msgR (u:(i:Fin n)→ Raw (T i))(j:Fin n): Texts:= ⟨T j,(E.Km (T j)).f (u j)⟩
include s H hv
lemma facedM(k:ℕ)(u:(i:Fin n)→ Raw (T i)): pErr E S T (fun i=>(E.Km (T i)).basic (u i)) k= errorP E S (msgR E T u) k:=by
    funext i; unfold pErr; simp_rw[MultilinearMap.sub_apply, Pins.idV]; rfl
-- any P.Uncontrolled projection
lemma readings(j:ℕ):rapid E.cc (conf n) (pErr E S T p) j:=by
    let I:Type:= (i:Fin n)→Raw (T i); let f(i):= (E.Km (T i)).basic
    let r(u:I):ℂ:=∏ i,(f i).repr (p i) (u i)
    let F(k:ℕ)(u:I):= E.errorP S (msgR E T u) k; have hm(u:I)(i:Fin n):Loaded E (msgR E T u i):=vouchers E (u i)
    have he(k:ℕ): E.pErr S T p k=∑ u,r u • F k u:=by
          funext y; unfold pErr; rw [YM.Fir.Lantern.expansion f,Finset.sum_apply]; apply Finset.sum_congr rfl
          intro u hu; change r u* E.pErr S T (fun i=>(E.Km _).basic (u i)) k y =_; rw[facedM hQ E S s H hv]; rfl -- signature
    intro K' hK h n₀ ε hε; let M:= ∑ u:I, ‖r u‖; have hx:0≤M:= sum_nonneg fun i _=> norm_nonneg _
    let A:= ε/(M+1); have hp:0<A:= div_pos hε (by linarith)
    filter_upwards [eventually_all.mpr fun u:I=> momentsD hQ E S (msgR E T u) (hm u) s H hv j K' hK h n₀ A hp] with k hk y hy
    have hc(u:I):ContDiffAt ℝ (j:ℕ) (F k u) y := period hQ E S _ (hm u) s H k j y (h hy)
    rw [he, iteratedFDeriv_sum_apply (u:=Finset.univ) (f:=fun u=>r u • F k u) (fun u _=>contDiffAt_const.smul (hc u)) ]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg (zero_le_one.trans (E.charge k)) n₀)).trans; rw [Finset.mul_sum]; apply le_trans (b:=(∑ u:I,‖r u‖*A)); refine Finset.sum_le_sum fun u _=>?_ ; rw [iteratedFDeriv_const_smul_apply (hc u), norm_smul]; exact le_trans (Eq.le (mul_left_comm ..)) (mul_le_mul_of_nonneg_left (hk u y hy) (norm_nonneg _))
    rw [← Finset.sum_mul]; change M*A≤ ε; apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num:(0:ℝ)≤1)) hp.le).trans; rw [mul_comm]; exact (div_mul_cancel₀ _ (ne_of_gt (by linarith))).le -- binder lex arg?
lemma pends(y:Points n)(ht:y∈conf n): Tendsto (fun k=>E.rCorr S T k y p) atTop (𝓝 (UV.Free.wick T y p)):=by
     apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards [readings hQ E S s H hv T p 0 (Set.singleton y) isCompact_singleton (Set.singleton_subset_iff.mpr ht) 0 (ε/2) (half_pos he)] with i hi; rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self he); have h:= hi y rfl; simp only[pErr,norm_iteratedFDeriv_zero,pow_zero,one_mul] at h; exact h
omit s H hv
lemma basisP:∀ j, rapid E.cc (conf n) (pErr E Q.total T p) j:=fun j=> readings hQ E Q.total (reliable hQ) (assay E) (measureE E) T p j
lemma sensorM (y:Points n)(ht:y∈conf n): Tendsto (fun k=>E.rCorr Q.total T k y p) atTop (𝓝 (UV.Free.wick T y p)):= pends hQ E Q.total (reliable hQ) (assay E) (measureE E) T p y ht
end Canopy
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Canopy.basisP
#print axioms YM.Intag.Sprig.Canopy.sensorM
