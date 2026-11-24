import YM.Kauri.Flux
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
open Org
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
local notation "Vd"=> K.level 8
local notation "U"=> Tarc K
local notation "pB"=> pulseB.toBasis
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
variable {p:End ℂ (Tarc K)}(h:Split p (Set.range (L0 A)))
-- preserves Pond
noncomputable def lake(T:Pollens P K):Submodule ℂ (Tarc K) where
    carrier:={x|Pond x T}
    zero_mem':=by
         have he(i:Hea):tee (0:Tarc K) i=0:=rfl; exact ⟨fun a b=>rfl,fun i=>map_zero _,fun i=> map_zero _,fun i a=>map_zero _,fun i=>by simp [he]⟩
    add_mem':=by
         rintro x y ⟨h1,h2,h3,h4,h5⟩ ⟨hx1,hx2,hx3,hx4,hx5⟩; refine ⟨fun a b=>by rw [tadd,tadd,h1 a b,hx1 a b],fun i=>?_,fun i=>?_,fun i j=>?_,fun i=>?_⟩ <;> first|(rw [tadd,map_add,h2,hx2])|(rw[tadd,map_add,h3,hx3])|(rw[tadd,map_add,h4,hx4])|(simp_rw [tadd,map_add,Finset.sum_add_distrib,h5,hx5,add_zero])
    smul_mem':=by
         rintro t x ⟨h1,h2,h3,h4,h5⟩; refine ⟨fun a b=>by rw[tsca,h1 a b,tsca],fun i=>?_,fun i=>?_,fun i j=>?_,fun i=>?_⟩ <;> first|(rw[tsca,map_smul,h2])|(rw [tsca,map_smul,h3])|(rw[tsca,map_smul,h4]) | (simp_rw [tsca,map_smul,← Finset.smul_sum,h5,smul_zero]) -- no nested smul!
include h J H JQ B R S
lemma feed :Pond (p (employ J)) T:=by
     have he: Pond (employ J) T:= by
             have hp:= strongT J; refine ⟨?_,?_,?_,?_,?_⟩<;>rw[hp]; exact J.n.tense.sym; exact J.n.tense.parity; exact J.n.tense.charge; exact J.n.tense.flux; exact soma W J.n
     let L:= lake T; have hg(x:End ℂ (Tarc K))(hf:Fet (Set.range (L0 A)) x):∀ y∈L,x y∈ L:=by
             induction hf with
             | mem i hs=> obtain ⟨p,rfl⟩:=hs; exact fun y hy=> wave J H JQ B R S hy p
             | zero=>exact fun _ _=> L.zero_mem
             | add _ _ _ _ hx hy =>exact fun x h=>L.add_mem (hx x h) (hy x h)
             | times _ _ _ _ hx hy=>exact fun x h=> hx _ (hy x h)
             | smul _ _ _ h=>exact fun x hx=> L.smul_mem _ (h x hx)
     change p _∈L; nth_rw 1 [show p=p-1+1 from by abel]; exact L.add_mem (hg (p-1) h.budget _ he) he
omit h
-- transported representation on level 8
variable (F:Free.Symbol 8≃ₗ[ℂ] ↥(K.level 8))(hf:Flyers A 8 le_rfl T F)
noncomputable def walt (L:Free.Symbol 8≃ₗ[ℂ] ↥(K.level 8)): EuPin→* (↥(K.level 8)≃ₗ[ℂ]↥(K.level 8)):=
   ⟨⟨fun p=> L.symm.trans ((caravan R 8 p).trans L),LinearEquiv.ext (fun x=>by simp)⟩,fun p q=>LinearEquiv.ext (fun x=>by
             change L (caravan R 8 (p*q) (L.symm x)) = L (caravan R 8 p (L.symm (L (caravan R 8 q (L.symm x)))))
             simp)⟩
set_option quotPrecheck false
local notation "A₀"=>tapeJ K W A (show 8≤8 from le_rfl)
include hf
lemma decide_f (t:EuPin)(x:K.level 8): (walt R F t x).val=ρ t x.val:=by
       rw[show walt R F t x= F (caravan R 8 t (F.symm x)) from rfl,← S.tones 8 le_rfl F hf t (F.symm x),LinearEquiv.apply_symm_apply]
-- orientation of original W discrete
include h
lemma dandy (t:EuPin)(s:Signed)(ht:t.Lifts s)(u:Tarc K) (hu:windP (dues t) (walt R F t) u=u):windP (dues t) (walt R F t) (p u) = p u:=by
       let Y:= windP (dues t) (walt R F t); let D:= orients s
       have he(g:Skew)(w:Tarc K):Y (L0 A g w)= L0 A (D g) (Y w):=by
             apply Mako.cowind _ _ (stall g) (stall (D g))
             · exact fun i=> (Eq.trans (stub g i t).symm (by rw[show t.coord=s.ortho from ht]; rfl))
             intro i; apply Subtype.ext; rw[decide_f J H JQ B R S F hf t]; change ρ t (A.jet _ _)= A.jet _ ((walt R F t _).val); rw[decide_f J H JQ B R S F hf t,S.acts JQ.h (loans J H JQ B R) t s ht]; exact halo_pin J H s t ht _ _
       change Y _=_; rw [←shack Y h _ _ u,show Y u=u from hu]
       · rintro i ⟨g,rfl⟩; exact ⟨_,⟨D g,rfl⟩,he g⟩
       rintro i ⟨g,rfl⟩; obtain ⟨z,rfl⟩:= Mako.flood s g; exact ⟨_,⟨z,rfl⟩,he z⟩
lemma camper(t:EuPin)(s:Signed)(ht:t.Lifts s)(x:BoxD): p (employ J) (dues t x)= walt R F t (p (employ J) x):=by
     let w:=employ J; have hp : windP (dues t) (walt R F t) w=w:=by
              apply (shoes _ _ _).mpr; intro x; suffices hv : w ∘ₗ (dues t).toLinearMap = (walt R F t).toLinearMap ∘ₗ w from DFunLike.congr_fun hv x; refine pulseB.toBasis.ext fun i=>?_ ; obtain ⟨i,j⟩:=i; apply Subtype.ext; change (w (troopL t _)).val= (walt R F t _).val; rw[sol, decide_f J H JQ B R S F hf, S.acts JQ.h (loans J H JQ B R) t s ht]; simp_rw[map_sum,map_smul,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; change (∑ a:Axis,∑ b:Axis,(↑(t.coord.val a i*t.coord.val b j):ℂ) • tee (employ J) (a,b))= T.spin t (tee (employ J) (i,j)); rw [strongT J,J.n.tense.geo t s ht]; exact Massive.Tarn.ChargeQ.EuM_w T W ρ (fun t s h=> S.acts JQ.h (loans J H JQ B R) t s h) i j t s ht -- arguments
     exact (shoes _ _ _).mp (dandy J H JQ B R S h F hf t s ht w hp) x -- signature
-- now extend connected action, use differential and growth lemma
lemma forge(t:EuPin)(x:BoxD): p (employ J) (dues t x)= walt R F t (p (employ J) x):=by
     let L:=walt R F; let Q:= p (employ J); let G(x:EuPin):Prop:=∀ v:BoxD,Q (dues x v)= L x (Q v); let UU:Subgroup EuPin:= {
          carrier:={x|G x},one_mem':=fun v=>by simp
          mul_mem':=by intro i j (hi:G i)(hj:G j) v; rw[map_mul,map_mul,LinearEquiv.mul_apply,hi,hj]; rfl
          inv_mem':=by intro j (he:G j) u; apply (L j).injective; rw [←he,←LinearEquiv.mul_apply,←map_mul]; simp }
     have ht:t∈UU:=by
            apply engenders UU (camper J H JQ B R S h F hf)
            intro g r v
            have hΛ (v:BoxD): (F.symm.toLinearMap ∘ₗ Q) (stall g v)= rain g 8 (F.symm (Q v)):=by
                  apply F.injective; rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hf.revenue,LinearEquiv.apply_symm_apply]; have hp: L0 A g * p =0:= h.hit _ ⟨g,rfl⟩; have he:= DFunLike.congr_fun (DFunLike.congr_fun hp (employ J)) v; exact (sub_eq_zero.mp he).symm
            apply F.symm.injective; let Y(t:ℝ):= F.symm (Q (dues (oathU g t) v)); let L':=(LinearMap.toContinuousLinearMap (rain g 8)).restrictScalars ℝ
            have hh(r): HasDerivAt Y (L' (Y r)) r:=by change HasDerivAt Y (rain g 8 _) r; unfold Y; rw[←hΛ]; exact ((F.symm.toLinearMap ∘ₗ Q).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (d_stall g (oathU g) (tour g) v r)
            let y(t):= caravan R 8 (oathU g t) (F.symm (Q v)); change Y r=F.symm (F (y r)); rw [F.symm_apply_apply, reaps L' Y hh r,reaps L' y (music g (tour g) R _) r]; congr 1; unfold Y y; simp [(tour _).1]
     exact (show G t from ht) x
lemma fully(t:EuPin)(a b:Axis): ρ t (tee (p (employ J)) (a,b))=∑ i:Axis,∑ j:Axis,(↑(t.coord.val i a*t.coord.val j b):ℂ) • tee (p (employ J)) (i,j):=by
       unfold tee; rw [← decide_f J H JQ B R S F hf t, ← forge J H JQ B R S h F hf]; change ((p _) (troopL t (pulseB.toBasis (a,b)))).val= _; rw [sol]; simp_rw [map_sum,map_smul,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; rfl
end YM.Kauri
#print axioms YM.Kauri.fully
#print axioms YM.Kauri.feed
