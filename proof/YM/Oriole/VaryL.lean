import YM.Oriole.Pic
import YM.Oriole.Tree
/-! Spatial central differences translation. Due specifically at STEP 0 relative.Taper dot.Jet.W.Meta. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG Wilson
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6){g:Bool}{c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
open QCD.Run QCD.Entr.Goals QCD.Creek MassiveQCD.Plate
local notation "K"=> Modes c 6
variable (x:Lat.Fields c 6)(r:ℝ)(hi:1≤r)
local notation "R"=> piece a b (uncoat x)
lemma bud_sq (i j:Fiber)(hi:1 ≤ r)(hy:2≤ n): ∑ p:Site c,∑ q: Site c, (1+max (pdist p:ℝ) (pdist q:ℝ))^2* ‖cell R p q i j‖ ≤ view 0 n x r:=by
    let f (p:Site c) : K:= ((p,i),a)
    let G(q:Site c): K:= ((q,j),b)
    let g : Site c × Site c → Finset (Pairs K):= fun x=>{Sum.inr (f x.1), Sum.inl (G x.2)}
    have hg: Injective g:=by
         intro p q he; have h1:(Sum.inr (f p.1))∈ g q:=he ▸ (by simp[g]:_∈g p); have h2:Sum.inl (G p.2)∈g q:=he ▸(by simp[g]:_∈g p); simp [g,f,G] at h1 h2; exact Prod.ext h1 h2
    let W(s:Finset (Pairs K)):= toll 0 n s r * ‖coef s x‖; let Y:= univ.image g
    apply le_trans (b:= ∑ s∈Y, W s)
    · rw [sum_image hg.injOn,Fintype.sum_prod_type]; refine sum_le_sum fun p _=> sum_le_sum fun q _=>?_
      let s:=g (p,q); change (1+max (pdist p:ℝ) (pdist q:ℝ))^2* ‖uncoat x _ _‖ ≤ (toll _ _ s r * _); have hζ : ‖coef s x‖ = ‖uncoat x (f p) (G q)‖:=by rw [ivory]; congr; ext u; simp [g,s]
      rw [show ‖uncoat x ((p,i),a) ((q,j),b)‖=‖coef s x‖ from hζ.symm] -- NOTE ←
      change _*‖coef s x‖ ≤ _; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      let E:=s.sup (Stew.lens (0:Site c)); have h1:pdist p≤ E:= le_trans (le_of_eq (show pdist p=Stew.lens (0:Site c) (Sum.inr (f p)) from (by change _=pdist (p-0); rw [sub_zero]))) (Finset.le_sup (f:=Stew.lens 0) (by simp [g,s]))
      have h2:pdist q≤ E:=le_trans (le_of_eq (show pdist q=Stew.lens (0:Site c) (Sum.inl (G q)) from (by change _=pdist (q-0); rw [sub_zero]))) (Finset.le_sup (f:=Stew.lens 0) (by simp [g,s])); have ht : (1+(E:ℝ))^2≤toll (0:Site c) n s r:=by
          unfold toll; apply (le_trans (b:= (1+(E:ℝ))^n) ?_ (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hi))); exact pow_le_pow_right₀ (by simp) hy
      have h1:(pdist p:ℝ)≤ E:=by exact_mod_cast h1
      have h2:(pdist q:ℝ)≤ E:=by exact_mod_cast h2 -- line parsing
      exact (pow_le_pow_left₀ (by positivity : 0≤1+max (pdist p:ℝ) (pdist q:ℝ)) (add_le_add_right (max_le h1 h2) _) 2).trans ht
    exact (Finset.sum_le_sum_of_subset_of_nonneg (f:=W) (s:=Y) (t:=(Finset.univ:Finset (Finset (Pairs K)))) (Finset.subset_univ _) (fun s _ _=> mul_nonneg (by unfold toll; positivity) (norm_nonneg _)))

-- shift of central cut charge. factory.M ≤ 400/ M. uses diff_t on both labels. all directions.
variable (H:Taper)(u v:Site c)(y:Cover)
local notation "β"=> wrap c y
local notation "χ" u:arg=> heat y u
local notation "η"=> Real.sqrt -- spare
local notation "Πu"=> u+β
local notation "Πv"=> v+β
local notation "I"=> (0:Multi d)
local notation "J"=> UV.first
variable (p q:Multi 8)
noncomputable def syrup (T:Taper)(p q:Multi d)(x:Cover)(u v:Site c):=heat x u*heat x v * Nw T p (u+wrap c x)*Nw T q (v+wrap c x)
noncomputable def chart (T:Taper)(p:Multi 8)(x:Cover)(u:Site c):ℂ:= Np T u * SourceRead.profile p (Lattice.lift u+x) 1
noncomputable abbrev vintage (T:Taper)(p q:Multi 8)(x:Cover)(u v:Site c):ℂ:= chart T p x u* chart T q x v
local notation "S"=>syrup H
local notation "V"=> vintage H
lemma braids (hx:∀ i:Axis,Int.natAbs (y i)≤ 1)(hp:8*(pdist u+2)< c.val)(hv:8*(pdist v+2)< c.val) : S p q y u v= vintage H p q y u v:=by
      obtain ⟨hu,ht,hU⟩:= charts u y H hx hp; obtain ⟨hv,hp,hV⟩:= charts v y H hx hv; let f(u:Site c) p:= SourceRead.profile (d:=8) p (Lattice.lift u) 1; change _= _; unfold syrup Nw; rw[show heat y u * heat y v * _ * _= (heat y u* Np H (u+β)* SourceRead.profile p (Lattice.lift (u+β)) 1)*(heat y v*Np H (v+β)*SourceRead.profile q (Lattice.lift (v+β)) 1) from (by ring)]; rw[hU,hV,ht,hp]; unfold vintage chart; rw[hu,hv]
lemma profile_0 (x:Cover): SourceRead.profile (0:Multi d) x 1=1:=by have hp(i:Axis): power (0:Multi d) i=0:=rfl; simp [SourceRead.profile,hp]
lemma profile_1(x:Cover)(j:Axis): SourceRead.profile (UV.first j) x 1=(x j:ℂ):=by unfold SourceRead.profile; rw [one_pow,one_mul, prod_eq_single j]; rw[nectar,if_pos rfl,pow_one,Nat.factorial_one]; simp; intro i _ h; rw[nectar,if_neg h.symm,pow_zero]; simp; simp
lemma flipT (i:Axis)(he:y=step i∨ y= -(step i)): pdist (wrap c y) ≤ 1∧∀ a:Axis, Int.natAbs (y a)≤1 :=by
      have hh := pdist_step (n:=c) i


      cases he with| inl h=> rw[h,wrap_step]; exact ⟨hh,fun j=> by simp [step_apply]; split <;> decide⟩|inr h=> rw [h,map_neg,wrap_step,pdist_neg]; exact ⟨hh,fun j=>by simp [step_apply]; split<;>decide⟩
lemma swipe (i j:Axis)(he:y=step i∨ y= -(step i)): ‖heat y u*Nw H (UV.first j) (u+β)‖ ≤ 1 + (pdist u:ℝ):=by
      have h:= (flipT (c:=c) y i he).1; have hx:‖heat y u‖=1:=by rcases (glares y|>.sign u) with h|h<;>simp[h]
      rw[norm_mul,hx,one_mul]; apply (QCD.Entr.Goals.N_price H (u+β) j).trans; exact_mod_cast (le_trans (pdist_triangle u β) (le_trans (Nat.add_le_add_left h _) (le_of_eq (Nat.add_comm ..))))
lemma sweep (q:Multi 8) (hH:q=0): ‖heat y u*Nw H q (u+β)‖≤1:=by
      have hx:‖heat y u‖=1:=by rcases (glares y|>.sign u) with h|h<;>simp [h]
      rw[norm_mul,hx, one_mul,hH, zeroN]; exact tintE ..
lemma slopeK (i j:Axis)(he:y=step i∨ y= -(step i)): ‖chart H (UV.first j) y u‖ ≤ 1+(pdist u:ℝ):=by
      have h:= (flipT (c:=c) y i he).2; unfold chart; rw [norm_mul,profile_1]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE u H)).trans; rw [Pi.add_apply,Int.cast_add]; apply (norm_add_le ..).trans; rw [add_comm]; rw [← Complex.ofReal_intCast (y j),← Complex.ofReal_intCast,Complex.norm_real,Complex.norm_real]; apply add_le_add _ (liftN ..); rw [Real.norm_eq_abs, ← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]; exact_mod_cast h j
lemma sloppy: ‖chart H 0 y u‖≤1:=by unfold chart; rw[profile_0,mul_one]; exact tintE ..
abbrev heart (p q:Multi 8):= spinWeight p + spinWeight q ≤8
lemma twoL (hx:heart p q) : p=0∧q=0 ∨ (∃ i:Axis,p=UV.first i ∧ q=0) ∨ (∃ i:Axis,p=0 ∧ q=UV.first i):=by
     have h:=low p; have he:=low q; unfold heart at hx; by_cases hz:p=0
     · by_cases h:q=0; · exact .inl ⟨hz,h⟩
       obtain ⟨i,hi⟩:= Oriole.halo q (by omega) h; exact .inr (.inr ⟨i,hz,hi.symm⟩)
     obtain ⟨i,hi⟩:= Oriole.halo p (by omega) hz; rw[← hi,juicy] at hx; exact .inr (.inl ⟨i,hi.symm,ground _ (by omega)⟩)
lemma rangeK(i:Axis)(hp: heart p q)(he:y=step i ∨ y= -(step i)): ‖S p q y u v‖≤1+max (pdist u:ℝ) (pdist v:ℝ) ∧ ‖V p q y u v‖≤1+max (pdist u:ℝ) (pdist v:ℝ):=by
     rw [syrup,show heat y u* _ * _*_= (heat y u*Nw H p (u+β))*(heat y v*Nw H q (v+β)) from (by ring), vintage,norm_mul (heat y u* _) (heat y v*_),norm_mul (chart H p _ _) _]; rcases twoL p q hp with h|h|h
     · obtain ⟨rfl,rfl⟩:=h; have hz:0≤ max (pdist u:ℝ) (pdist v:ℝ):=by positivity
       exact ⟨(mul_le_one₀ (sweep H u y 0 rfl) (norm_nonneg _) (sweep H v y 0 rfl)).trans (le_add_of_nonneg_right hz),(mul_le_one₀ (sloppy H u y) (norm_nonneg _) (sloppy H v y)).trans (le_add_of_nonneg_right hz)⟩ -- `sweep` last arg
     · obtain ⟨j,h,h'⟩:=h; rw[h,h']; exact ⟨ ((mul_le_of_le_one_right (norm_nonneg _) (sweep H v y 0 rfl)).trans (swipe H u y i j he)).trans (add_le_add_right (le_max_left ..) _), ((mul_le_of_le_one_right (norm_nonneg _) (sloppy H v y)).trans (slopeK H u y i j he)).trans (add_le_add_right (le_max_left ..) _)⟩
     obtain ⟨j,h,h'⟩:=h; rw[h,h']; exact ⟨ ((mul_le_of_le_one_left (norm_nonneg _) (sweep H u y 0 rfl)).trans (swipe H v y i j he)).trans (add_le_add_right (le_max_right ..) _), ((mul_le_of_le_one_left (norm_nonneg _) (sloppy H u y)).trans (slopeK H v y i j he)).trans (add_le_add_right (le_max_right ..) _)⟩
lemma yield(i:Axis)(hp:heart p q)(he:y=step i∨ y= -(step i)): ‖S p q y u v-V p q y u v‖≤ 32/(c.val:ℝ)*(1+max (pdist u:ℝ) (pdist v:ℝ))^2:=by
     by_cases h:8*(pdist u+2)< c.val ∧ 8*(pdist v+2)<c.val
     · rw [braids H u v y p q ((flipT (c:=c) y i he).2) h.1 h.2,sub_self,norm_zero]; positivity
     let x:=1+max (pdist u:ℝ) (pdist v:ℝ); have hX:0≤x:=by unfold x; positivity
     obtain ⟨hy,hV⟩:= rangeK H u v y p q i hp he; have hw: (c.val:ℝ) ≤ 16*x:=by
          unfold x; push Not at h; by_cases hp: 8*(pdist u+2)< c.val
          · have ht : (c.val:ℝ)≤ 8*(pdist v+2:ℝ):=by exact_mod_cast h hp
            have hu: (pdist v:ℝ) ≤ max (pdist u:ℝ) (pdist v:ℝ):=le_max_right ..; linarith [Nat.cast_nonneg (α:=ℝ) (pdist v)]
          have he: (c.val:ℝ) ≤ 8*(pdist u+2:ℝ):=by exact_mod_cast Nat.le_of_not_lt hp
          linarith [le_max_left (pdist u:ℝ) (pdist v:ℝ),Nat.cast_nonneg (α:=ℝ) (pdist u)]
     apply (norm_sub_le ..).trans ((add_le_add hy hV).trans ?_); change x+x ≤ 32/(c.val:ℝ)*x^2; rw[div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; nlinarith only [mul_le_mul_of_nonneg_left hw hX]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.yield
#print axioms YM.Massive.Oriole.bud_sq
