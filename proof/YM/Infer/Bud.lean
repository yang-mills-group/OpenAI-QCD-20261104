import YM.Infer.Trinity
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
local notation "V₁"=> rayM C.S d e
set_option quotPrecheck false
local notation "Ω" i:arg => (C.A i).regulator
local notation "ℓθ"=> 24
variable {S} {n:ℕ} (P:Calibration C) (D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))(v:Fin n→Bool)(k:Fin n)(f:Fin n→ Cover)(i:ℕ)
variable (B:Invest (Uv.display C Ht sym U base) (D k))
local notation "XF" u:arg f:arg i:arg=>kerH Pκ D u k f i
variable (ε:ℝ)(hε:0<ε)
abbrev paper (X: Sequence)(P: Calibration X)(d:ℕ)(g:ℕ→Submodule ℂ (Label d)): Prop := ∀ (n:ℕ)(D:Fin n→ℕ)(k: Fin n)(h:d=D k)(u:(i:Fin n)→Label (D i)), ∀ (r:ℝ),0 < r →∀ ε:ℝ,0 < ε → ∀ᶠ i:ℕ in atTop,∀ y:Fin n→ Cover,localSep X i y r→ ∀ V ∈ g i, ‖V‖≤1→ ‖kerH P D u k y i (h ▸ V)‖≤ ε
abbrev dizzy (Q:Calibration C)(V:ℕ→Submodule ℂ (Label (D k))): Prop:=∀ᶠ j in atTop,∀ ε:ℝ,0 < ε →∀ᶠ i:ℕ in atTop,∀ x:Fin n→ Cover, seaM C i j x→∀ y∈V i,‖y‖≤1→ ‖kerH Q D u k x i y‖≤ ε
noncomputable abbrev Invest.grove (Y: Invest P d)(i:ℕ):= Submodule.span ℂ (Set.range (Y.bonds i))
lemma minted (i:ℕ)(Y:Label (D k))(h:Y ∈ B.grove Pκ i):∃ L:Fin (deficit (D k))→ℂ,(∑ j,L j • B.bonds i j)=Y:=by -- namespace dot arg P binds?
    let f:= B.bonds i
    refine Submodule.span_induction (s:= Set.range f) ?_ ?_ ?_ ?_ h; rintro x ⟨j,rfl⟩; exact ⟨Pi.single j 1, by simp [f]⟩
    · exact ⟨0,by simp⟩
    · rintro x y _ _ ⟨A,rfl⟩ ⟨X,rfl⟩; exact ⟨A+X,by simp only [Pi.add_apply,add_smul,sum_add_distrib]⟩
    rintro z x _ ⟨A,rfl⟩; exact ⟨z • A,by simp only [smul_sum, smul_smul,Pi.smul_apply, smul_eq_mul]⟩
lemma twirls (i:ℕ)(x: Fin n→ Cover)(j: Fin n)(V Z:Label (D j))(q:Label (D k))(he:j≠k) :
  kerH P D (update u j (V+Z)) k x i q=kerH P D (update u j V) k x i q+kerH P D (update u j Z) k x i q:=by
   change metricP C _ _ _ _ _= metricP C _ _ _ _ _+metricP C _ _ _ _ _; rw [update_comm he, update_comm he,update_comm he]; exact each D _ _ _ 0 _ _ _ _ -- j param i unused ambiguity
include hs hC hY hX
local notation "Zq"=> B.grove Pκ
lemma flask (hw:∀ i,i≠k→moored (u i).val (v i)): dizzy D u k Pκ Zq:=by
    by_cases h:∀ i,i≠k → u i≠0
    · apply (marchu Ht Uv sym base U hX hY hs hC D u v k B hw h).mono -- fix
      intro j h ε he
      filter_upwards [h ε he] with i hi xo hx y hv ht; obtain ⟨p,rfl⟩:= minted Ht Uv sym base U D k B i y hv; exact hi xo hx p ht
    push_neg at h; obtain ⟨t,ht,h⟩:=h; exact Eventually.of_forall (fun j ε he=> Eventually.of_forall fun i x hx y hv hr=> by change ‖metricP C Pκ D (update u k y) i x‖≤_; rw [gone Pκ D x i _ t (by rw [update_of_ne ht,h]),norm_zero]; exact he.le)
lemma premiered (T:Finset (Fin n))(h : k∈T)(hp:∀ i,i∉T→∃ p:Bool,moored (u i).val p): dizzy D u k Pκ Zq:=by
    -- recursion avoiding k. upgrade
    have h₀(T:Finset (Fin n))(u:(i:Fin n)→ Label (D i))(h:k∉T)(hp:∀ i,i∉T→i≠k→∃ p:Bool,moored (u i).val p): dizzy D u k Pκ Zq:=by
       induction T using Finset.induction_on generalizing u with
       | empty=> choose! p hP using hp; exact flask Ht Uv sym base U hX hY hs hC D u p k B (fun i hn=> hP i (notMem_empty i) hn)
       | insert a S hs ih=>
           have hk:k ≠ a:= fun e=> h (mem_insert.mpr (Or.inl e)); have hsx:k∉ S:= fun hh=>h (mem_insert.mpr (Or.inr hh)); let X(p):= facing sym p (u a); let V(p):= update u a (X p)
           have hV p:= ih (V p) hsx (fun i hi hi'=>by
                  by_cases he:i=a; · subst i; unfold V; rw [update_self]; exact ⟨p,fronting ..⟩
                  unfold V; rw [update_of_ne he]; exact hp i (by simp [he,hi]) hi')
           filter_upwards [hV true,hV false] with j hx hz; intro ε he; filter_upwards [hx _ (half_pos he),hz _ (half_pos he)] with i hj hv x hX w hy ha
           let F(p):= (XF p x i) w; change ‖F u‖≤_; have hf:F u= F (V true)+F (V false):=by
              have hh:=twirls Pκ D u k i x a (X true) (X false) w (Ne.symm hk); rwa [show X true+X false=u a from (revelation ..).symm,update_eq_self] at hh
           rw [hf]; exact (norm_add_le ..).trans ((add_le_add (hj x hX w hy ha) (hv x hX w hy ha)).trans_eq (add_halves _))
    apply h₀ (T.erase k) u (notMem_erase _ _); intro i hi hk; exact hp i (fun he=>hi (mem_erase.mpr ⟨hk,he⟩))
omit hs hC hY hX
include hs hC hY hX
lemma ghost (d:ℕ)(V:Invest (Uv.display C Ht sym U base) d):paper C Pκ d (V.grove Pκ):=by
    intro n D k h u r hv ε he
    subst d; obtain ⟨N,h⟩:= eventually_atTop.mp (premiered Ht Uv sym base U hX hY hs hC D u k V _ (mem_univ k) (fun i hi=>(hi (mem_univ i)).elim))
    obtain ⟨j,hj,hX⟩:= shyness hC r hv N; filter_upwards [h j hj ε he,hC.uv.tendsto_atTop.eventually_ge_atTop j] with i hi hx X hU y h h₁; exact hi _ (tide _ _ _ hU hx hX) y h h₁
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.ghost
