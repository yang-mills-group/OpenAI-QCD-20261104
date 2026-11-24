import YM.Vern.Vue
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {φ:ℕ→ℕ}
variable (hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable {d:ℕ}
noncomputable def safeV (T:Pollens P K) : Submodule ℂ K.W where
    carrier :={x|T.parity x=x ∧∀ f:FlavorTorus,T.flavor f x=x}
    zero_mem':= ⟨map_zero _,fun _=> map_zero _⟩
    add_mem' :=by rintro x y ⟨h,h'⟩ ⟨e,e'⟩; refine ⟨?_,fun i=>?_⟩ <;>first|(rw[_root_.map_add,h,e])|(rw [_root_.map_add,h',e'])
    smul_mem':=by rintro c x ⟨h,h'⟩; exact ⟨(map_smul ..).trans (congr_arg _ h),fun i=>(map_smul ..).trans (congr_arg _ (h' i))⟩
noncomputable def seedP (T:Pollens P K)(d:ℕ):Submodule ℂ ↥(K.level d):=(safeV T).comap (K.level d).subtype
noncomputable def seatP(d:ℕ):Submodule ℂ (Free.Symbol d):= (Qa d).map projection
variable (p:Free.Symbol d)
lemma edges(k:ℕ):p∈seatP d ↔ X.frame k d p∈seedP T d:=by
      let W:= X.frame k d; let B:= X.base d; let u:=B.liftS p; have hp:projection u=p:= B.right p
      have h:=X.leaders k d; constructor
      · rintro ⟨t,hv,ht⟩; have hx:=(show Tawny.Quiet t.val from hv); change projection t=p at ht; rw[← ht]; exact ⟨(h.spins t).trans (congr_arg (fun x:Label d=>(W (projection x)).val) (Subtype.ext ((P.sym.parityActs d t).trans hx.1))),fun i=>(h.turns t i).trans (congr_arg (fun x:Label d=>(W (projection x)).val) (Subtype.ext ((P.sym.flavorActs d i t).trans (hx.2 i))))⟩
      intro he; have he:(W p).val∈ safeV T:= he; rw [←hp] at he; obtain ⟨hx,hy⟩:= he; refine ⟨u,?_,hp⟩; change Tawny.Quiet u.val
      let L:=B.liftS.comp projection; have hp' : u=L u:=congr_arg B.liftS hp.symm
      refine ⟨?_,fun i=>?_⟩
      · have h₀ : projection (P.sym.parity d u)=projection u:= W.injective (Subtype.ext ((h.spins u).symm.trans hx)); rw [←P.sym.parityActs]; have h₂:= (congr_arg (P.sym.parity d) hp').trans ((B.aligned.parity u).symm); exact congr_arg Subtype.val (h₂.trans ((congr_arg B.liftS h₀).trans hp'.symm))
      have h₀ : projection (P.sym.flavor d i u)=projection u:= W.injective (Subtype.ext ((h.turns u i).symm.trans (hy _))); rw [← P.sym.flavorActs]; have h₂:=(congr_arg (P.sym.flavor d i) hp').trans ((B.aligned.flavor u i).symm); exact congr_arg Subtype.val (h₂.trans ((congr_arg B.liftS h₀).trans hp'.symm))
noncomputable def simV (k d:ℕ):↥(seatP d)≃ₗ[ℂ]↥(seedP T d):=by
      let W:=X.frame k d; refine {toFun:=fun x=> ⟨W x.val, (edges E X x.val k).mp x.property⟩,invFun:=fun x=>⟨W.symm x.val, (edges E X (W.symm x.val) k).mpr ?_⟩,left_inv:=fun x=>Subtype.ext (W.symm_apply_apply x.val),right_inv:=fun x=>Subtype.ext (W.apply_symm_apply _),map_add':=fun x y=>Subtype.ext (map_add W _ _),map_smul':=fun c x=>Subtype.ext (map_smul W _ _) }
      change W _∈_; rw [LinearEquiv.apply_symm_apply]; exact x.property
#check simV
local notation "a₀"=> timeAxis
include hf HQ
private lemma θx (p q:EuPin)(h:p.coord=q.coord)(s:Signed)(hs:p.Lifts s)(v:K.W)(he:T.parity v=v): T.spin p v=T.spin q v:=by
      have ht:q.Lifts s:= h.symm.trans hs; obtain hz|hz:= tolerates T HQ.h p s hs q ht; · rw[hz]
      rw[hz]; change T.parity (T.spin q v) =_; rw [spinClamp T HQ.h q s ht,he]
variable (i:Tri)
set_option quotPrecheck false
local notation "G"=> SpinQ i
lemma flow_t : Ortho.move (SpinQ i).coord (basis timeAxis)= basis timeAxis:=by
      rw [show (SpinQ i).coord= (Cup i).ortho from (fL i)]; have h:StressFlux.sign (Cup i) timeAxis=1:=(coreTime i).2; rw [StressFlux.signed_basis,(coreTime i).1,h,one_smul]
lemma flash (v:K.W)(he:T.parity v=v): T.spin (SpinQ i) (T.adj timeAxis v)= T.adj timeAxis (T.spin (SpinQ i) v):=by
      have hv := fL i; let Z:= flipC timeAxis; let U:= SpinQ i; have hf':Z.Lifts (Signed.mirror a₀):=couture _; have h₁:T.parity (Ch T a₀ v)= Ch T a₀ v:=by change T.parity (T.spin Z (T.adj a₀ v))= T.spin Z (T.adj a₀ v); rw [spinClamp T HQ.h Z _ hf',eyeP T HQ.h a₀,he]; -- inspect
      have hT : T.spin U (Ch T a₀ v)= Ch T a₀ (T.spin U v):=by
             obtain ⟨c,hc⟩:=tinted T HQ.h a₀ U _ hv; rw [hc]; split; rw [spinClamp T HQ.h U _ hv, h₁]; rfl
      rw[←steal T HQ.h a₀ v, ←steal T HQ.h a₀ (T.spin U v),← hT]; change (T.spin U*T.spin Z) _ =(T.spin Z*T.spin U) _; rw [←T.spine HQ.h _ _ _ _ hv hf',← T.spine HQ.h _ _ _ _ hf' hv]; apply θx hf HQ _ _ _ (Cup i*Signed.mirror a₀) (EuPin.life_mul hv hf') _ h₁
      rw[show (U*Z).coord= _ from (EuPin.life_mul hv hf'),show (Z*U).coord= (Signed.mirror a₀*Cup i).ortho from (EuPin.life_mul hf' hv)]; congr 1; -- decide sign concrete using permutations
      apply Signed.ext; · apply Equiv.ext; intro j; fin_cases i<;> fin_cases j<;>rfl
      funext j; fin_cases i<;>fin_cases j<;> rfl
lemma tips (r:ℝ)(hr:0<r) (v u:K.W)(he:T.parity v=v): turf timeAxis r (T:=T) (T.spin (SpinQ i) v) (T.spin (SpinQ i) u)= turf timeAxis r (T:=T) v u:=by
      let A:= points (![0,r • basis a₀]); have hx : A∈conf 2:= DawnS.distinct r hr; have hz:=hf.discrete 2 A hx G _ (fL i) (![T.adj a₀ v,u])
      unfold turf; rw [← flash hf HQ i v he]; rw [show Points.move (G).coord A=A from ?_] at hz; refine Eq.trans ?_ hz; apply congr_arg; funext i; fin_cases i<;>rfl
      apply PiLp.ext; intro j; fin_cases j; exact map_zero (Ortho.motion ..); exact (map_smul (Ortho.motion ..) r (basis timeAxis)).trans (congr_arg (r • ·) (flow_t hf HQ i))
end YM.Vern
#print axioms YM.Vern.tips
#print axioms YM.Vern.simV
