import YM.Iceberg.Grey
import YM.Iceberg.Peat
set_option quotPrecheck false
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
variable (A:Persona T V)
variable (i j a:Axis)
noncomputable def mirage (a:Axis)(p:Face):ℂ:= ((signT (Signed.mirror a) p.1*signT (Signed.mirror a) p.2):ℝ)
lemma mirW (p:Face): mirage a p*mirage a p=1:=by unfold mirage; push_cast; rw [mul_mul_mul_comm,mirror_sq,mirror_sq,mul_one]
local notation "UA"=>P.sym.adj 8 a
lemma blush (p:Face)(k:ℕ): let w:=(ouzel V E X A k).val p; P.sym.adj 8 a w = mirage a p • w :=by
      intro w; let J:=T.adj a; let c:=mirage a p; let y:ℝ:= mintS V E X A k
      have hV: J (V p)=c • V p:=by
           have hx : c • J (V p)=V p:=congr_fun (A.real'a a) p; rw[show c • V p=c • (c • J (V p)) from congr_arg (c • ·) hx.symm,smul_smul,show c*c=1 from mirW a p,one_smul]
      let F:= X.frame k 8; have ht(z:Label 8): (F (projection z)).val= bullet E X 8 k z:=rfl
      have he: T.adj a (bullet E X 8 k w) = bullet E X 8 k (P.sym.adj 8 a w):= (X.leaders k 8).reflects w a
      have hv:projection (UA w)=c • projection w:=F.injective (Subtype.ext (by rw[map_smul,Submodule.coe_smul,ht,ht,←he,show bullet E X 8 k w= (↑y:ℂ) • V p from spyR ..,map_smulₛₗ,show starRingEnd ℂ (↑y:ℂ)=(↑y:ℂ) from Complex.conj_ofReal _,show T.adj a (V p)=_ from hV]; exact smul_comm ..))
      let X':=(X.base 8).liftS; have hw :w=X' (projection w):= pearS ..
      have hc:=Eq.trans (congr_arg (P.sym.adj 8 a) hw) ((X.base 8).aligned.adj w a).symm
      change UA w=X' (projection (UA w)) at hc; rw [hv,map_smul, ← hw] at hc; exact hc
-- SL continuity aux
lemma slate {X:Type}[NormedAddCommGroup X] [NormedSpace ℂ X][FiniteDimensional ℂ X](p:X≃ₛₗ[starRingEnd ℂ]X): Continuous p:=by
    let F:= Module.finBasis ℂ X; have h(x):p x=∑ i, star (F.coord i x) • p (F i):=by
               conv_lhs=>arg 2; rw[← F.sum_repr x]
               rw[map_sum]; apply Finset.sum_congr rfl; intro i _; exact map_smulₛₗ ..
    rw [show (p:X→X)=_ from funext h]; exact continuous_finsetSum _ (fun i _=> ((F.coord i).continuous_of_finiteDimensional.star).smul continuous_const) -- path
variable (f:ℕ→ℕ)(R:RawTensor 1 8)(hR:∀ i:Face,Tendsto (fun k:ℕ=>(ouzel V E X A (f k)).val i) atTop (𝓝 (R.val i)))
include hR V
lemma aureate (p:Face): P.sym.adj 8 a (R.val p)= mirage a p • (R.val p):=by
     have h:Tendsto (fun k:ℕ=> P.sym.adj 8 a ((ouzel V E X A (f k)).val p)) atTop (𝓝 (P.sym.adj 8 a (R.val p))):= ((slate _).continuousAt (x:=R.val p)).tendsto.comp (hR p) -- arg
     simp_rw[fun i:ℕ=>blush V E X A a p i] at h -- A order?
     exact tendsto_nhds_unique h (tendsto_const_nhds.smul (hR p))
lemma basin (u:ℂ)(x: Flavor 6→ℂ)(h:symbS 1 R= Hail.shore u x) : star u=u∧star x=x:=by
      apply pinsW; funext ⟨b,i⟩; let k:Face:=(b,i); let a:=timeAxis; let J(w:Label 8):= P.sym.adj 8 a w; let z:=Hail.flood u x
      have hz:projection (R.val k)= projection (z.val k):= congr_fun h k
      have he :projection (J (R.val k))=projection (J (z.val k)):=by
            let F:= X.frame 0 8; apply F.injective; apply Subtype.ext; exact Eq.trans ((X.leaders 0 8).reflects _ a).symm (Eq.trans (congr_arg (fun v:Free.Symbol 8=>T.adj a (F v).val) hz) ((X.leaders 0 8).reflects _ a))
      let c:=mirage a k; let v:=Hail.flood (star u) (star x); have ht : J (z.val k)=c • v.val k:=by unfold c mirage; push_cast; exact shrubs x u a b i P.sym -- order
      rw [show J (R.val k)= c • R.val k from aureate V E X A a f R hR k,ht,map_smul,map_smul,hz] at he
      apply smul_right_injective (M:=Free.Symbol 8) (show c≠0 from by intro h; have hh:c*c=1:=mirW ..; rw[h,zero_mul] at hh; exact zero_ne_one hh) he.symm -- binder
omit hR V
lemma unStar (p:ℂ)(hp:star p=p): (p.re:ℂ)=p:=by
      have ht := congr_arg Complex.im hp
      rw [Complex.star_def,Complex.conj_im] at ht; apply Complex.ext; rfl; simp only [Complex.ofReal_im]; linarith
variable (W:Face→Free.Symbol 8)(h:Tendsto (fun i=> aceG V E X (f i) A.tense) atTop (𝓝 W))(hZ:Tendsto f atTop atTop)
include hp hP hHQ ht hf h hZ A V
open Heron
lemma icon (hy:onceF K (V (0,0))=0):∃ (κ:IceT→ℝ)(R:RawTensor 1 8), symbS 1 R=W ∧ symbS 1 R=symbS 1 (bendP (fun i=>(κ i:ℂ))) ∧∀ j:Face,Tendsto (fun i:ℕ=>(ouzel V E X A (f i)).val j) atTop (𝓝 (R.val j)):=by
     obtain ⟨R,hr,hV⟩:= yarn V E X A f W h; let x:=points (![0,(1:ℝ) • basis timeAxis]); have hx:x∈conf 2:= DawnS.distinct 1 zero_lt_one
     obtain ⟨p,u,hW⟩:= Hail.cliff R P.sym (fun d t=>(Canopy.adornV T E hp ht hP hHQ hf t _).mp) (bankV hHQ V E X A f hZ R hV x hx) (stand hHQ V E X A f hZ R hV _ hy)
     obtain ⟨hg,hv⟩:= basin V E X A f R hV p u hW; refine ⟨fun i=>i.elim (-p.re) (fun i=> -(u i).re),R,hr,?_,hV⟩; rw[hW,Hail.shore,bent]; apply congr_arg; apply congr_arg; funext i; cases i <;>first| (simp [unStar p hg,fun i=>unStar (u i) (congr_fun hv i)]; done)|rfl
end YM.Iceberg
#print axioms YM.Iceberg.icon
