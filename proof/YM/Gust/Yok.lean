import YM.Gust.Tundra
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Table Work.A01 Outer Tarn Tarn.Choir UV
open scoped Topology ContDiff BigOperators Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){n m:ℕ}
variable (A:Axis×Axis→K.W)(hA:Tarn.ChargeQ.Persona T A) (J:Axle K (fun a b=>A (a,b)))(U:Vane J)(x:Points (m+1))(hx:x∈conf _)(v:Fin (m+1)→K.W)(s:Fin (m+1)→Bool)(hp:∀ i,v i∈ Col T (s i))
variable (l a b:Axis)(g:Ortho.Skew) (ht:Ward.onLine l x)
include hK in
lemma by_color (v:K.W):∃ x∈Col T true,∃ y∈Col T false,v=x+y:=by
       let x:=T.parity v; let c:ℂ:=2⁻¹
       refine ⟨c • (v-x), ?_,c • (v+x), ?_,?_⟩
       · rw[hue,map_smul,map_sub,T.even hK,show tauMod true=(-1:ℂ) from rfl, neg_one_smul,←smul_neg,neg_sub]
       · rw[hue,map_smul,map_add,T.even hK,show tauMod false=(1:ℂ) from rfl,one_smul,add_comm (T.parity v)];
       rw [←smul_add, show v-x+(v+x)= (2:ℂ) • v from by rw[two_smul]; abel,smul_smul]; norm_num [c]
noncomputable def whirlK(t:E4):K.W→ₗ[ℂ]K.W:= J.jet g+∑ i:Axis,(M4.move g.val t i:ℂ) • U.edge i
lemma wind(t:E4)(v:K.W): whirlK A J U g t v= swirl K A J U g t v:=by simp only [whirlK,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,swirl]
noncomputable def zenT: MultilinearMap ℂ (fun _:Fin (m+1)=>K.W) ℂ:=∑ i:Fin (m+1),(K.total _ x).compLinearMap (update (fun _=> LinearMap.id) i (whirlK A J U g (x i)))
lemma za: valor A J U x v g= zenT A J U x g v:=by
       unfold valor zenT; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg; ext1 j; by_cases h:j=i; · subst j; rw[update_self,update_self,wind]
       rw[update_of_ne h,update_of_ne h]; rfl
include hx hA hf hK ht
lemma shills(he:a≠b): valor A J U x v (Ortho.plane b a)=0:=by
       let p:=Ortho.plane b a; rw[za]; let X:=zenT A J U x p
       choose! u hu w hw hV using fun i=> by_color (T:=T) hK (v i) -- args
       rw [show v=u+w from funext hV]; change X (u+w)=0; rw [X.map_add_univ]; apply Finset.sum_eq_zero; intro s _; let β(i: Fin (m+1)):= decide (i∈s); let f := s.piecewise u w; have h(i:Fin (m+1)) : f i∈Col T (β i):=by
              by_cases h:i∈s; · simpa [f,h,β] using hu i
              simpa [f,h,β] using hw i
       change X f=0; rw [←za]; exact quake hK hf A hA J U x hx f β h a b l he ht
-- sum plane linearity without W Norm real patch
noncomputable abbrev turnQ(x:E4)(i:Axis): Ortho.Skew→ₗ[ℝ]ℝ where
     toFun g:= M4.move g.val x i
     map_add' g t:= congr_arg (fun y:E4=>y i) (StressFlux.Annular.turn_add g t x)
     map_smul' g t:= congr_arg (fun y:E4=>y i) (StressFlux.Annular.turn_smul t g x)
lemma line : valor A J U x v g=0:=by
       let P(i:Fin (m+1)):= (K.total _ x).toLinearMap v i
       let R(i:Fin (m+1)): Ortho.Skew →ₗ[ℝ]ℂ:= {
            toFun t:= P i (J.jet t (v i))
            map_add':=fun t u=>by rw [J.addP hf hK,LinearMap.add_apply,map_add] -- linearMap + apply.
            map_smul':=fun t u=>by rw [J.scaleP hf]; change P i ((t:ℂ) • _)= t • (P i _); rw [map_smul]; rfl }
       let W(i:Fin (m+1)):= ∑ b:Axis,(turnQ (x i) b).smulRight (P i (U.edge b (v i))); let C:=∑ i:Fin (m+1),(R i+W i)
       have H(g): valor A J U x v g=C g:=by
             unfold C; rw [LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_; change P i (J.jet g (v i)+_)=_; unfold W; rw [map_add,map_sum,LinearMap.add_apply,LinearMap.sum_apply]; congr 1; apply Finset.sum_congr rfl; intro b _; rw [map_smul]; rfl
       rw [H]; have hh:C=0:=by
            apply Spin.extendsE; intro i; obtain ⟨b,a⟩:=i; by_cases h:a=b; · subst b; rw [show Spin.K (a,a)=0 from Subtype.ext (by simp[Spin.K,Ortho.plane]),map_zero,map_zero]
            exact (H _).symm.trans (shills hK hf A hA J U x hx v l a b ht h)
       rw[hh]; rfl
end YM.Massive.Gust
#print axioms YM.Massive.Gust.line
