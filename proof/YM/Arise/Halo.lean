import YM.Arise.Mark
import YM.Analysis.Multilinear
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
-- Two-types of aperture.St.S powers smooth.
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F] -- math arbitrary F
noncomputable def ameet (p:PlaqAxes)(x:E4→F)(y:E4): F:= ∫ s in (0:ℝ)..1, ∫ r in (0:ℝ)..1, x (y+(s • basis p.val.1+r • basis p.val.2))
noncomputable def zoom (a: Option PlaqAxes)(f:E4→F): E4→F:= match a with | some p=>ameet p f|none=> f
lemma rot_s (p:PlaqAxes)(f:E4→F)(y:E4)(h:Continuous f): Continuous (fun s:ℝ=>∫ r in (0:ℝ)..1,f (y+(s • basis p.val.1+r • basis p.val.2))):=by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry; fun_prop
lemma zoom_add (a:Option PlaqAxes)(f g:E4→F)(h:Continuous f)(hp: Continuous g): zoom a (f+g)=zoom a f+zoom a g:=by
    cases a with
    | none=>rfl
    | some p=> funext x; change ameet p (f+g) x=_; unfold ameet; simp only [Pi.add_apply,zoom,ameet]; have hl(t:ℝ):=(h.comp (show Continuous fun r:ℝ=> x+(t • basis p.val.1+r • basis p.val.2) by fun_prop)).intervalIntegrable (μ:=volume) (0:ℝ) 1; have hg(t:ℝ):=(hp.comp (show Continuous fun r:ℝ=> x+(t • basis p.val.1+r • basis p.val.2) by fun_prop)).intervalIntegrable (μ:=volume) (0:ℝ) 1; simp_rw [show ∀ s:ℝ, (∫ r in (0:ℝ)..1,(f (x+(s • basis p.val.1+r • basis p.val.2))+g (x+(s • basis p.val.1+r • basis p.val.2))))=_ from fun s=>intervalIntegral.integral_add (hl s) (hg s)] -- compositions
               rw [intervalIntegral.integral_add ((rot_s p f x h).intervalIntegrable ..) ((rot_s p g x hp).intervalIntegrable ..)]
lemma zoom_smul (a:Option PlaqAxes)(f:E4→F)(r:ℝ):zoom a (r • f)=r • zoom a f:=by cases a with |none=>rfl|some p=> funext x; simp only [zoom,ameet,Pi.smul_apply,intervalIntegral.integral_smul]
lemma accommodate (a:Option PlaqAxes) (l:List Axis)(E:T E4 F l.length)(h:Tensor.Sym E) (z:Cover): sound (zoom a (diagonal E) ∘ gross) (strike l z)=l.length.factorial • E (basis ∘ l.get):=by
    have he:= (diag_smooth E ∞).continuous
    cases a with
    | none=> simpa only [Function.comp_def,zoom,add_zero] using plow l E h z 0
    | some p=>simp only [Function.comp_def,zoom,ameet]; rw [sail] -- twice
              let G(i:Cover)(s r:ℝ):= diagonal E (gross i+(s • basis p.val.1+r • basis p.val.2)); have hv(s:ℝ):sound (fun i=>∫ r in (0:ℝ)..1,G i s r) (strike l z)=l.length.factorial • E (basis ∘ l.get):=by rw [sail _ (fun i=>G i s) (fun i=> he.comp (show Continuous fun r:ℝ=>gross i+(s • basis p.val.1+r • basis p.val.2) by fun_prop))]; unfold G; simp_rw [plow l E h]; rw [intervalIntegral.integral_const,sub_zero,one_smul]
              change (∫ s in (0:ℝ)..1,sound (fun i=>∫ r in (0:ℝ)..1,G i s r) (strike l z))=_; simp_rw [hv]; rw [intervalIntegral.integral_const,sub_zero,one_smul]; rfl
              exact fun i=> rot_s p _ (gross i) he
lemma accustomed (a:Option PlaqAxes)(l:List Axis)(h:j<l.length)(E:T E4 F j)(hp:Tensor.Sym E)(z:Cover): sound (zoom a (diagonal E) ∘ gross) (strike l z)=0:=by
    have he:= (diag_smooth E ∞).continuous
    cases a with
    | none=> simpa only [Function.comp_def,zoom,add_zero] using higher l h E hp z 0
    | some p=>simp only [Function.comp_def,zoom,ameet]; rw [sail]
              let G(i:Cover)(s r:ℝ):= diagonal E (gross i+(s • basis p.val.1+r • basis p.val.2)); have hv(s:ℝ):sound (fun i=>∫ r in (0:ℝ)..1,G i s r) (strike l z)=0:=by rw [sail _ (fun i=>G i s) (fun i=> he.comp (show Continuous fun r:ℝ=>gross i+(s • basis p.val.1+r • basis p.val.2) by fun_prop))]; unfold G; simp_rw [higher l h E hp]; simp
              change (∫ s in (0:ℝ)..1,sound (fun i=>∫ r in (0:ℝ)..1,G i s r) (strike l z))=_; simp_rw [hv]; simp
              exact fun i=> rot_s p _ (gross i) he
-- scalar ℝ linear. No norm needed later.
def Lore (F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F](i:ℕ):Submodule ℝ (T E4 F i) where
   carrier:={X| Tensor.Sym X}
   zero_mem':=fun _ _=> rfl
   add_mem':=fun {_ _} h g v p=> congr_arg₂ (fun a b:F=>a+b) (h v p) (g v p)
   smul_mem':=fun r _ h v p=>congr_arg (fun a:F=> r • a) (h v p)
noncomputable def stare (p:Option PlaqAxes)(v:Parc)(i:ℕ): Lore ℝ i→ₗ[ℝ] ℝ where
    toFun T:= sound (zoom p (diagonal T.val) ∘ gross) v
    map_add' T S:= by change sound (zoom p (diagonal T.val+diagonal S.val)∘ gross) v=_; rw [zoom_add _ _ _ (diag_smooth _ ∞|>.continuous) (diag_smooth _ ∞|>.continuous)]; exact fond ..
    map_smul' r T:= by change sound (zoom p (r • diagonal T.val)∘ gross) v=_; rw [zoom_smul]; exact vital ..
noncomputable abbrev Peg (i:ℕ) := (Lore ℝ i)→ₗ[ℝ] ℝ
noncomputable def stares (p:Option PlaqAxes)(i:ℕ): Parc→ₗ[ℝ] Peg i where
    toFun v:=stare p v i
    map_add' _ _:= LinearMap.ext fun _=>map_add (sound _) _ _
    map_smul' _ _:= LinearMap.ext fun _=>map_smul (sound _) _ _
lemma spectra (a:Option PlaqAxes)(i:ℕ)(z:Cover): Submodule.span ℝ (Set.range fun f:Fin i→Axis=>stare a (strike (List.ofFn f) z) i)=⊤:=by
    let D(f:Fin i→Axis):=stare a (strike (List.ofFn f) z) i
    let A:=Submodule.span ℝ (Set.range D); apply Submodule.eq_top_of_finrank_eq; have hx: A.dualCoannihilator = ⊥:=by
       refine le_antisymm (fun u hu=>Submodule.mem_bot ℝ|>.mpr ?_) bot_le
       apply Subtype.ext; change u.val=0; let E:=u.val
       have h1 (f:Fin i→Axis) := (Submodule.mem_dualCoannihilator _).1 hu (D f) (Submodule.subset_span ⟨f,rfl⟩)
       apply ContinuousMultilinearMap.ext; intro v; let X:=(EuclideanSpace.basisFun Axis ℝ).toBasis; rw [show E v=_ from Multilabel.expansion (fun _=>X) E.toMultilinearMap v]; refine sum_eq_zero fun w _=>?_ -- rw fail?
       have he(l:List Axis)(h:l.length=i): sound (zoom a (diagonal E) ∘ gross) (strike l z) = i.factorial • E (basis ∘ l.get ∘ Fin.cast h.symm):=by subst i; exact accommodate a l E u.property z
       have hp:= h1 w; change sound _ (strike _ _) =_ at hp; -- use he
       have hw (l:List Axis)(h1:l.length=i) : sound (zoom a (diagonal E) ∘ gross) (strike l z)= _:= he l h1 -- same
       have hE: i.factorial • E (basis ∘ w)=0:= by
           rw [show basis ∘ w = basis ∘ (List.ofFn w).get ∘ Fin.cast (List.length_ofFn (f:=w)).symm from ?_, ← he _ List.length_ofFn]; exact hp
           funext i; simp
       have he1: E (basis ∘ w)=0:=by rw [← Nat.cast_smul_eq_nsmul ℝ,smul_eq_mul] at hE; exact (mul_eq_zero.mp hE).resolve_left (by positivity)
       rw [show E.toMultilinearMap _= E (basis ∘ w) from congr_arg E (funext fun i=> show X (w i)=_ from EuclideanSpace.basisFun_apply ..), he1]; exact smul_zero _
    have hu := Subspace.finrank_add_finrank_dualCoannihilator_eq A; rw [hx,finrank_bot,Nat.add_zero] at hu; exact hu.trans (Subspace.dual_finrank_eq ..).symm
-- Layer construction: like Mom.Truth. Explicit linear comb of longer with all anchors.S.S obsc
noncomputable def tails (n d:ℕ): Submodule ℝ Parc:=Submodule.span ℝ {x|∃ (l:List Axis) (p:Cover),n ≤ l.length∧l.length ≤ d∧x=strike l p}
lemma tailUp (h:r ≤ n)(ht:d ≤ m): tails n d ≤ tails r m:= Submodule.span_mono fun w hw=> by obtain ⟨l,p,hL,hF,hm⟩:=hw; exact ⟨l,p,h.trans hL,hF.trans ht,hm⟩
structure Rocky (p:Option PlaqAxes)(l:List Axis)(n:ℕ)(X:Parc): Prop where
     rest : X-strike l 0 ∈tails (l.length+1) (n+1)
     stops k : k ≤ n → l.length < k → stare p X k=0
lemma drops (p:Option PlaqAxes)(h:j<n) (X:Parc)(hp:X∈ tails n d): stares p j X=0:=by
    refine Submodule.span_induction (p:=fun x _=> stares p j x=0) ?_ (by simp) (fun x y _ _ h ht=>by simp [map_add,h,ht]) (fun a x _ h=>by rw [map_smul,h,smul_zero]) hp
    rintro x ⟨l,v,hp,hv,rfl⟩; exact LinearMap.ext fun M=> accustomed p l (h.trans_le hp) M.val M.property _
lemma chooses (p:Option PlaqAxes)(l:List Axis)(n:ℕ) : ∃ X:Parc, Rocky p l n X:=by
    induction n with
    | zero=> exact ⟨_,⟨show strike l 0-strike l 0 ∈ tails (l.length+1) (0+1) by simp,fun _ _ _=>by omega⟩⟩
    | succ n ih=>
      obtain ⟨w,h⟩:=ih; by_cases hp:l.length ≤ n; swap
      · refine ⟨strike l 0, by constructor; simp; intros; omega⟩
      let u:=n+1; let Z:=tails u u; let V:=stares p u
      have hs : stare p w u ∈ Z.map V:= by
             have he: Submodule.span ℝ (Set.range fun f:Fin u→Axis=>stare p (strike (List.ofFn f) 0) u)≤ Z.map V:=by refine Submodule.span_le.mpr ?_; rintro x ⟨f,rfl⟩; refine Submodule.mem_map.mpr ⟨strike (List.ofFn f) 0,Submodule.subset_span ⟨_,_,le_of_eq ((List.length_ofFn ..).symm),List.length_ofFn (f:=f) |>.le,rfl⟩,rfl⟩
             exact he ((spectra p u 0).symm ▸ Submodule.mem_top)
      obtain ⟨b,hb,hq⟩:=Submodule.mem_map.mp hs; refine ⟨w-b,⟨?_,?_⟩⟩
      · rw [sub_right_comm]; exact Submodule.sub_mem _ (tailUp le_rfl (Nat.le_succ _) h.rest) (tailUp (Nat.add_le_add_right hp 1) (Nat.le_succ _) hb)
      intro k hk hx; obtain hk|rfl:= hk.lt_or_eq
      · change stares _ _ _=_; rw [map_sub, drops p hk _ hb,sub_zero]; exact h.stops _ (Nat.le_of_lt_succ hk) hx
      change V (w-b)=0; rw [map_sub,hq]; exact sub_self _ -- hq direction and name.Z disappears
lemma received (p:Option PlaqAxes)(l:List Axis)(n:ℕ)(X:Parc)(h:Rocky p l n X):stare p X l.length=stare p (strike l 0) l.length:= sub_eq_zero.mp ((map_sub (stares p l.length) _ _).symm.trans (drops _ (Nat.lt_succ_self _) _ h.rest))
lemma rests (p:Option PlaqAxes)(l:List Axis)(n:ℕ)(X:Parc)(h:Rocky p l n X)(ht:i ≤n)(he:l.length ≠ i):stare p X i=0:=by
     obtain hv|hv:= lt_or_gt_of_ne he; exact h.stops i ht hv
     have hp := drops p (Nat.lt_succ_of_lt hv) _ h.rest; rw [map_sub] at hp; exact (sub_eq_zero.mp hp).trans (LinearMap.ext fun v=> accustomed p l hv v.val v.property 0)
end YM.Arise
#print axioms YM.Arise.chooses
