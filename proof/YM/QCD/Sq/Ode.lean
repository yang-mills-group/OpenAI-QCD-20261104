import YM.QCD.Sq.Peg
/-! # square existence -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sq
open Filter Function Set Finset
open scoped Topology Classical BigOperators
local notation "𝔹" => Twin
abbrev Span:=↥Tate
noncomputable def band (x:ℝ):ℝ:= max (-1) (min 1 x)
lemma banded (t:ℝ): |band t| ≤1:= abs_le.mpr ⟨le_max_left .., max_le (by linarith) (min_le_left ..)⟩
lemma belt (s:ℝ)(h:s∈Tate):band s=s:=by rw [band,min_eq_right h.2,max_eq_right h.1]
noncomputable def tap (r:ℝ):Span:=⟨band r,abs_le.mp (banded _)⟩
lemma tapped (r:ℝ)(he:|r| ≤1):(tap r).val=r:=belt _ (abs_le.mp he)
@[fun_prop] lemma tap_cont : Continuous tap:=by unfold tap band; fun_prop
noncomputable def spin (k n:ℕ):Span:=tap (-1+(k:ℝ)*2/n)
lemma spin₀ (n:ℕ):(spin 0 n).val = -1:=by unfold spin; simp [tap,band] -- inspect
lemma spotG {i n:ℕ}(hp:0<n)(hv:i≤n): (spin i n).val = -1+(i:ℝ)*2/n:=by
    have hn :0 < (n:ℝ):= Nat.cast_pos.mpr hp
    have hi :(i:ℝ) ≤ n:= Nat.cast_le.mpr hv
    apply belt; change _ ≤ _∧ _ ≤_; constructor; · exact le_add_of_nonneg_right (by positivity)
    linarith only [(div_le_iff₀ hn).mpr (by linarith only [hi] : (i:ℝ)*2≤ 2*n)]
lemma spin₁ {n:ℕ}(hn:0<n):(spin n n).val=1:=by rw [spotG hn le_rfl]; have hh: (n:ℝ)>0:=(by exact_mod_cast hn); field_simp; linarith only
lemma weave {k n:ℕ}(h:k<n): dist (spin k n) (spin (k+1) n)=2/n:=by
   have hp:0<n:=(by omega); have hx:0<(n:ℝ):=by exact_mod_cast hp
   rw [Subtype.dist_eq, Real.dist_eq, spotG hp (by omega), spotG hp (Nat.succ_le_of_lt h)]; rw [show - (1:ℝ)+ _-( -1+(↑(k+1):ℝ)*2/n)= -(2/(n:ℝ)) from ?_,abs_neg,abs_of_pos (by positivity)]; -- first args order
   push_cast; ring
noncomputable def ray (A:𝔹)(i:Bool):ℝ:= if i then mast A else tail A
theorem beam (f:𝔹→𝔹)(h:Continuous f)(hg:∀ a:𝔹,∀ i,|ray a i|=1 → ray (f a) i=ray a i):∃ x:𝔹,tail (f x)=0∧mast (f x)=0:=by
    by_contra hp; push Not at hp
    have hx : Continuous (fun i=> Sq.floor (f i)):=by unfold Sq.floor; fun_prop
    let w:Twin:= ⟨tap 0,tap 0⟩; obtain ⟨o,ho,hP⟩:= isCompact_univ.exists_isMinOn (f:=fun i=> Sq.floor (f i)) (Set.nonempty_iff_ne_empty.mpr (show univ≠(∅: Set Twin) from Set.nonempty_iff_ne_empty.mp ⟨w,Set.mem_univ _⟩)) hx.continuousOn
    let c:=Sq.floor (f o); have hc : 0 < c:=by by_cases h:tail (f o)=0; · exact lt_of_lt_of_le (abs_pos.mpr (hp _ h)) (le_max_right ..)
                                               exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_left ..)
    obtain ⟨δ,hδ,h⟩:= Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous h) _ hc
    obtain ⟨n,hn⟩:=exists_nat_gt (2/δ); have hh :0<(n:ℝ):= (div_pos (by positivity) hδ).trans hn; have he:0<n:=Nat.cast_pos.mp hh
    let s (i j :ℕ):𝔹:= (spin i n,spin j n); let p i j:=coat (f (s i j)); have hx : 2/(n:ℝ) < δ:= (div_lt_iff₀ hh).mpr (by linarith only [(div_lt_iff₀ hδ).mp hn])
    have hs(A B:Twin)(ht:dist A B< δ): coat (f B) ≠ rev (coat (f A)):=closeT _ _ (h ht) (hP (Set.mem_univ A)) (hP (Set.mem_univ B)) hc
    have hY i a (u:ℝ) (h:|u|=1)(hv:ray a i=u): ray (f a) i=u:=(hg a i (hv.symm ▸ h)).trans hv
    refine rect n p ?_ ?_ ?_ ?_ ?_ he
    · intro i hi j hj
      have ht:dist (spin i n) (spin (i+1) n)<δ:= (weave hi).trans_lt hx; have hE:dist (spin j n) (spin (j+1) n)<δ:= (weave hj).trans_lt hx
      unfold p; refine ⟨hs _ _ ?_,hs _ _ ?_,hs _ _ ?_,hs _ _ ?_,hs _ _ ?_⟩ <;> (simp only [s, Prod.dist_eq,dist_self,max_lt_iff]; exact by tauto)
    · intro i hi; exact leftX _ (hY false (s 0 i) (-1) (by simp) (spin₀ _))
    · intro i hi; exact rightX _ (hY false (s n i) 1 (by simp) (spin₁ he))
    · intro i hi; exact downX _ (hY true (s i 0) (-1) (by simp) (spin₀ _))
    intro i hi; exact upX _ (hY true (s i n) 1 (by simp) (spin₁ he))
end YM.QCD.Sq
#print axioms YM.QCD.Sq.beam
