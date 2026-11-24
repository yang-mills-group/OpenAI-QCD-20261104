import YM.QCD.Sq.Ode
/-! # face permanence extension across holes. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sq
open Filter Function Set Finset
open scoped Topology Classical BigOperators
local notation "𝔹"=>Twin
variable {G:𝔹→𝔹}{P: Set Twin}
section real
variable {F f:Twin→ℝ}
lemma life (h:ContinuousOn f P)(hp:IsClosed P)(he:Continuous F)(hr: EqOn f F (P∩{i| |F i|=1})): ∃ g :Twin→Span,Continuous g ∧EqOn g (tap ∘ f) P ∧∀ i, |F i|=1→(g i).val=F i:=by
    let A:Set Twin:={i| |F i|=1}; have hA:IsClosed A:= isClosed_eq he.abs continuous_const
    let v:=P.piecewise f F; have h1:EqOn v f P:=piecewise_eqOn _ _ _
    have h2:EqOn v F A:=by
        intro x hx; by_cases hu:x∈P; · exact (h1 hu).trans (hr ⟨hu,hx⟩)
        exact Set.piecewise_eq_of_notMem _ _ _ hu
    let S:= P∪ A; let T : C(S,ℝ):=⟨S.restrict v,continuousOn_iff_continuous_restrict.mp ((continuousOn_union_iff_of_isClosed hp hA).mpr ⟨h.congr h1,he.continuousOn.congr h2⟩)⟩
    obtain ⟨g,hg⟩:=T.exists_restrict_eq (hp.union hA); have hk : EqOn g v S:=fun i hh=> DFunLike.congr_fun hg (⟨i,hh⟩:S); exact ⟨tap∘g, tap_cont.comp g.continuous, fun i hh=>congr_arg tap ((hk (Or.inl hh)).trans (h1 hh)),fun i hh=>(congr_arg (fun s=>(tap s).val) ((hk (Or.inr hh)).trans (h2 hh))).trans (tapped (F i) hh.le)⟩
lemma mint (hp:IsClosed P)(hx:Continuous F)(hf:ContinuousOn f P)(ht:∀ i∈ P,(F i=1→1≤ f i) ∧(F i=-1→ f i ≤ -1)):∃ g:Twin→Span,Continuous g∧EqOn g (tap ∘ f) P ∧∀ i,|F i|=1→ (g i).val=F i:=by
    have hh:ContinuousOn (fun i=>(tap (f i)).val) P:= (continuous_subtype_val.comp tap_cont).comp_continuousOn hf -- edit
    have hQ: EqOn (fun i=>(tap (f i)).val) F (P ∩ {i| |F i|=1}):=by
        rintro i ⟨hi,hp⟩
        change (tap (f i)).val=F i; rcases eq_or_eq_neg_of_abs_eq (show _= (1:ℝ) from hp) with hb|hb
        · rw [hb]; dsimp only [tap,band]; rw [min_eq_left ((ht i hi).1 hb), max_eq_right (by norm_num : -(1:ℝ)≤1)]
        rw [hb]; dsimp only [tap,band]; have h1:= (ht i hi).2 hb; rw [min_eq_right (by linarith : f i≤1),max_eq_left h1]
    obtain ⟨g,h,hE,hG⟩:= life hh hp hx hQ
    refine ⟨g,h,fun i hi=> (hE hi).trans (Subtype.ext (tapped (tap (f i)).val (abs_le.mpr (tap (f i)).2))),hG⟩

end real
abbrev Rune (i:Bool)(t:Twin):= ray t i
lemma cohere (A B:Twin→Twin) (h:∀ i j,|ray (A i) j|=1 → ray (B i) j=ray (A i) j)(hv:∀ i j,|ray i j|=1→ ray (A i) j=ray i j):∀ i j,|ray i j|=1 → ray (B i) j=ray i j:=by
    intro i j hx; exact (h i j ((hv i j hx).symm ▸ hx)).trans (hv i j hx)
lemma mirrorP (X:𝔹→𝔹)(f g:Twin→ℝ)(hp:ContinuousOn f P)(hh:ContinuousOn g P)(hx:Continuous X)(hP:IsClosed P)(h:∀ i∈P,(tail (X i)=1→1≤f i) ∧(tail (X i)=-1→f i≤ -1))(ht:∀ i∈P,(mast (X i)=1→1≤g i)∧(mast (X i)=-1→g i≤ -1)):∃ F:Twin→Twin, Continuous F ∧ EqOn F (fun i=>(tap (f i),tap (g i))) P∧ ∀ i j,|ray (X i) j|=1 → ray (F i) j=ray (X i) j:=by
    obtain ⟨Y,hY,hF,h1⟩:= mint hP (show Continuous (fun i=>tail (X i)) from cont_tail.comp hx) hp h
    obtain ⟨K,hK,hV,h2⟩:= mint hP (show Continuous (fun i=>mast (X i)) from cont_mast.comp hx) hh ht
    exact ⟨fun i=>(Y i,K i),hY.prodMk hK,fun i hh=> Prod.ext (hF hh) (hV hh),fun i j=>by cases j; exact h1 i; exact h2 i⟩
def Walls (A:Twin):Prop:=∃ i,|ray A i|=1
lemma glance (i:ℝ)(h:¬ |i|≤1): |(tap i).val|=1:=by
    by_cases hv:i≤1; · dsimp only [tap,band]; rw [min_eq_right hv,max_eq_left ?_,abs_neg,abs_one]; exact le_of_lt (lt_of_not_ge fun hh=>h (abs_le.mpr ⟨hh,hv⟩))
    dsimp only [tap,band]; rw [min_eq_left (le_of_not_ge hv),max_eq_right (by norm_num : -(1:ℝ)≤1),abs_one]
lemma awake {g X:Twin→Twin} (h:∀ i j,|ray (g i) j|=1 → ray (X i) j=ray (g i) j){x}(hp: Walls (g x)):Walls (X x):=by obtain ⟨i,hp⟩:=hp; rw [← h x i hp] at hp; exact ⟨_,hp⟩
end YM.QCD.Sq
