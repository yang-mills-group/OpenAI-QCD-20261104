import YM.Sprig.June
/-! Build precise weak bases from raw maps and keep the covariance spent so far. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder ContDiff
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
open Compass
variable {β e:ℝ}(hc:C.Path β e)(hφ:Tendsto φ atTop atTop)(hP:P.System)(hQ:Q.Harmony P φ)(hv:Foil P Q T)
variable (n:Side)(he:Injective (P.candidate d n 0))
variable (F:Qua P d)
open YM.Intag.Vale
noncomputable def snowH (k:ℕ):Free.Symbol d →ₗ[ℂ] ↥(Q.level d):= (Q.focus none d).rangeRestrict ∘ₗ (E.V k d) ∘ₗ F.liftS
lemma sails(k:ℕ)(x:Free.Symbol d): (snowH E F k x).val=E.cut k (F.liftS x):=rfl
private theorem archer {X Y:Type}[AddCommGroup X][AddCommGroup Y][Module ℂ X][Module ℂ Y][FiniteDimensional ℂ X][FiniteDimensional ℂ Y] (f:X→ₗ[ℂ]Y)(h: Module.finrank ℂ X=Module.finrank ℂ Y)(hf:∀ x, f x=0→x=0):Bijective f:=by
     have hv :Injective f:= LinearMap.ker_eq_bot.mp (bot_unique fun x hx=> hf x hx); exact ⟨hv, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1 hv⟩
include hQ
set_option maxHeartbeats 650000
-- invertible due W-Gram.
lemma arises : ∀ᶠ i in atTop,Bijective (snowH E F i):=by
     let A:=E.La d; let J:=E.Ja d
     let Qc(i):= snowH E F i
     let f(i:Stokes d):= (A.F i).mark
     let g(i:Stokes d):= P.sym.adj _ timeAxis (f i)
     let y:= basis timeAxis; let p:= points (![0,y]); have hP:p∈conf 2:= by have h:=DawnS.distinct 1 zero_lt_one; convert h using 1; unfold DawnS.dotsG DawnS.prelude; rw[one_smul]; -- p reducible?
     let H(k:ℕ)(i j:Stokes d):= Q.total 2 ((E.B k).r • p) (![cut E k (g i),(Qc k (A.B j)).val])
     have hh (i j:Stokes d) : Tendsto (fun k=>H k i j) atTop (𝓝 (ΦGram P.sym A y i j)):=by
           have hx:= bonus E hQ (g i) (F.liftS (A.B j)) p hP; have he:readK p (g i) (F.liftS (A.B j))=ΦGram P.sym A y i j:=Eq.trans (DawnS.trails _ hP (![g i,F.liftS (A.B j)]: (k:Fin 2)→ UV.Label ((fun _=>d) k)) (![g i, f j]) (fun k=>by fin_cases k; rfl; exact (F.right (A.B j)).trans (A.h j))) rfl
           rw [he] at hx; exact hx
     filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (fun j=> (hh i j).eventually (Metric.closedBall_mem_nhds _ J.light)))] with k hk
     have he : nearG P.sym A J.ε (H k):=fun i j=> by have ht:=Metric.mem_closedBall.mp (hk i j); rw[dist_eq_norm] at ht; exact ht
     refine archer (X:=UV.Free.Symbol d) (Y:=↥(Q.level d)) (snowH E F k) (hQ.h.faith d).symm ?_
     · intro x hy; let q(i: Stokes d) := A.B.coord i x; have hq:∑ i:Stokes d, q i • A.B i=x:= A.B.sum_repr x
       have ht:Γ (H k) q=0:=by
           funext j; let Z:= Q.total 2 ((E.B k).r • p); let T:= (![cut E k (g j),0]); let L:↥(Q.level d)→ₗ[ℂ]ℂ:= (Z.toLinearMap T 1) ∘ₗ (Q.level d).subtype
           have hx(i):H k j i= L (snowH E F k (A.B i)):=by unfold H; apply congr_arg Z; funext l; fin_cases l<;>simp [T,Qc]
           change ∑ i:Stokes d,H k j i*q i=0; simp_rw [hx, mul_comm _ (q _),← smul_eq_mul,← map_smul,←map_sum,hq, show snowH E F k x=0 from hy,map_zero]
       have hh: q=0:=(norm_le_zero_iff).mp (le_trans (J.warmth he q) (by rw[ht,norm_zero,mul_zero])); change x=0; rw[←hq, hh]; simp
structure Prose (p: Free.Symbol d≃ₗ[ℂ] ↥(Q.level d))(T:Pollens P Q):Prop where
    rotates x s r (h:s.Lifts r) : T.spin s (p (projection x))= (p (projection (P.sym.pin d s x))).val
    turns x u : T.flavor u (p (projection x))= (p (projection (P.sym.flavor d u x))).val
    jumps x : T.charge (p (projection x))= (p (projection (P.sym.charge d x))).val
    spins x : T.parity (p (projection x))= (p (projection (P.sym.parity d x))).val
    reflects x a : T.adj a (p (projection x))= (p (projection (P.sym.adj d a x))).val
    unit : (p (projection (P.sym.unit d))).val= lampU P Q
open Prose
include hv
lemma chose :∃ p:ℕ→Free.Symbol d≃ₗ[ℂ] ↥(Q.level d), (∀ i,Prose (p i) T)∧∀ᶠ i in atTop,(p i).toLinearMap=snowH E F i:=by
    let f(k:ℕ):= snowH E F k
    have ht:∀ᶠ k:ℕ in atTop,∃ p:Free.Symbol d≃ₗ[ℂ]↥(Q.level d), Prose p T∧p.toLinearMap=f k:=by
         filter_upwards [arises E hQ F, cut_unit (d:=d) E, cut_pin (d:=d) T E, cut_adj (d:=d) T E, cut_flavor (d:=d) T E, cut_charge (d:=d) T E, cut_parity (d:=d) T E] with i hi hu hp hs ht hC hZ
         let p:= LinearEquiv.ofBijective (f i) hi; have h(x: Symbol d): (p x).val= E.cut i (F.liftS x):=rfl
         let u:= F.liftS.comp projection; have hq(x:Label d): (p (projection x)).val= E.cut i (u x):= h _
         refine ⟨p,⟨fun x p s h=>?_,fun x v=>?_,fun x=>?_,fun x=>?_,fun x a=>?_,?_⟩,rfl⟩ -- h shadow
         · rw [hq,hq,← hp _ _ _ h,show P.sym.pin d p (u x)=u (P.sym.pin d p x) from (F.aligned.pin _ _ _ h).symm]
         · rw [hq,hq,← ht,show P.sym.flavor d v (u x)= u (P.sym.flavor d v x) from (F.aligned.flavor ..).symm]
         · rw [hq,hq,← hC,show P.sym.charge d (u x)= u (P.sym.charge d x) from (F.aligned.charge ..).symm]
         · rw [hq,hq,← hZ,show P.sym.parity d (u x)= u (P.sym.parity d x) from (F.aligned.parity ..).symm]
         · rw [hq,hq,← hs,show P.sym.adj d a (u x)= u (P.sym.adj d a x) from (F.aligned.adj ..).symm]
         rw [hq, show u (P.sym.unit d)=P.sym.unit d from F.aligned.unit, hu, hv.unit]
    obtain ⟨N,hN⟩:=eventually_atTop.mp ht; choose p hP hk using hN
    let g(i:ℕ):=p (max i N) (le_max_right ..); refine ⟨g,fun i=>hP _ (le_max_right ..),?_⟩; refine (eventually_ge_atTop N).mono fun i hi=> (hk _ (le_max_right i N)).trans ?_ ; unfold f; rw[max_eq_left hi]
end YM.Sprig
#print axioms YM.Sprig.chose
