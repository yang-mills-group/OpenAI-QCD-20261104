import YM.QCD.Entr.Left
/-! # Rotor germs glue at full labels. No K merge until log repairs incorporated. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n:ℕ}{p:BudgetPoint}{η u a r t w P q J:ℝ}{i j x:Site c}{X:Support c}
open Revolve Villa Port
abbrev Silo (c:Side):= Land c (Site c) (Site c)
abbrev BankP (c:Side):= Pays c (Site c) (Site c)
abbrev Tick (c:Side):= Site c × Site c × Support c
noncomputable def dispatch (q: Tick c): RegularAddress c:= ⟨q.1,if q.1∈ q.2.2 ∧ q.2.1∈ q.2.2 then q.2.2 else {q.1},by split <;> rename_i h; exact h.1; exact mem_singleton_self _⟩
noncomputable def fareP (Γ:Silo c)(q:Tick c)(V:Grid c): Bundle:= Γ q.1 q.2.1 q.2.2 (settled V)
def flopT (q:Tick c): Tick c:= (q.2.1,q.1,q.2.2)
noncomputable def pairQ (Γ:Silo c)(q: Tick c)(V:Grid c): Sheet c:= Stew.block q.1 q.2.1 (fareP Γ q V)
noncomputable def gleam (Γ:Silo c)(V:Grid c)(q:Tick c): Sheet c:= ((2:ℝ)⁻¹) • (pairQ Γ q V+pairQ Γ (flopT q) V)
noncomputable def sealG (Γ:Silo c)(N:ℕ) : Gem c N (Tick c):= ⟨dispatch,fun i V=> paleF N (gleam Γ V i)⟩
lemma foldedS (X Y:Sheet c)(k:ℝ)(h:X=foldH Y)(hv:Y=foldH X): k • (X+Y)=foldH (k • (X+Y)):=by
    unfold foldH; change (k:ℂ) • (X+Y)=foldH ((k:ℂ) • (X+Y)); unfold foldH; rw [Matrix.conjTranspose_smul,show star (k:ℂ)=k from by simp,Matrix.mul_smul,Matrix.smul_mul, Matrix.conjTranspose_add, Matrix.mul_add,Matrix.add_mul,show terraL _ * Xᴴ * _=Y from hv.symm, show terraL _ * Yᴴ * _=X from h.symm,add_comm]
lemma fold_cell (Γ:Silo c)(ht:Torch Γ)(q:Tick c)(V:Grid c): pairQ Γ (flopT q) V= foldH (pairQ Γ q V):=by
    have hh(a): fareP Γ a V=J0*star (fareP Γ (flopT a) V)*J0:=by unfold fareP flopT; nth_rw 1 [← ht.2]; simp only [seed,fullT]
    unfold foldH; nth_rw 2 [← terraJ (D:=Site c)]; unfold terraL; apply whist; intro i j; rw [pairQ, pairBl,hh,cell_ride_right,cell_ride_left]; simp only [Equiv.refl_apply]; rw [cell_flip, pairQ, pairBl,cT]; change (if i=q.2.1 ∧ j=q.1 then _ else _) = _; split
    next h=> rw [if_pos h.symm,mul_assoc]; simp only [mul_assoc]; rfl
    next h=> rw [if_neg (show ¬ (j=q.1 ∧ i=q.2.1) from fun hh=>h hh.symm),star_zero,mul_zero,zero_mul]
lemma dusted (c:Side)(N:ℕ)(U:Sheet c)(hp:U=foldH U): Regal c N (paleF N U)= paleF N U:=by
   apply Subtype.ext
   let Y:=idol c N; change disguise Y (surf _ (form (Lat.copies N U)))=form (Lat.copies N U); rw [surf_form,show star (Lat.copies N U)= Y*Lat.copies N U *star Y from (copies_star ..).symm.trans (duality N hp).1, disguise,form_map, Matrix.transpose_transpose]; have hx: star Y*Y=1:=white.1; simp only [Matrix.mul_assoc,hx,mul_one]; rw [← Matrix.mul_assoc (star Y),hx,one_mul]
noncomputable def wheelS (s:Strut c): Equiv.Perm (Tick c):=Equiv.prodCongr (act s) ((act s).prodCongr (Equiv.finsetCongr (act s)))
lemma trill (s:Strut c)(x:Tick c):wheelS s x=(act s x.1, act s x.2.1,x.2.2.image (act s)):=by unfold wheelS; refine Prod.ext rfl (Prod.ext rfl ?_); change Equiv.finsetCongr (act s) _=_; simp [Finset.map_eq_image]
lemma wheeled (s:Strut c)(x: Tick c): dispatch (wheelS s x)=rotateL (dispatch x) s:=by
   rw [trill]; unfold dispatch rotateL; simp only; congr 1; by_cases h:x.1∈x.2.2 ∧ x.2.1∈x.2.2
   · rw [if_pos h,if_pos]; exact ⟨mem_image_of_mem _ h.1, mem_image_of_mem _ h.2⟩
   rw [if_neg h, if_neg (show ¬_ from fun ht=> h ⟨(by simpa using ht.1),(by simpa using ht.2)⟩)]; exact (image_singleton ..).symm
lemma motion (Γ:Silo c)(h:Torch Γ)(s:Strut c)(g:Site c→ℂ)(W:Spike)(hh:Warrant s g W)(V: Grid c)(q:Tick c): fareP Γ q (sky s V)=lightP s W g q.1*fareP Γ (wheelS s q) V *star (lightP s W g q.2.1):=by
    let p:= singleR c; have ht:= hygiene s; let i:=q.1; let j:=q.2.1; let z:=q.2.2; let E:=Γ i j z (settled (sky s V)); let L:=lightP s W g
    have he : fareP Γ (wheelS s q) V=star (L i)*E*L j:=by
       have hh:= h.1.kept s g W (ht.symm ▸ hh) V ((Bay.sun p).shiftP s i) ((Bay.sun p).shiftP s j) (raiseS p s z); unfold driveD at hh; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply] at hh; unfold Bay.sun at hh; simp only at hh; unfold p at hh; unfold raiseS at hh; rw [ht] at hh; simp only [Equiv.finsetCongr_apply, Equiv.coe_toEmbedding,Finset.map_eq_image,tips,still] at hh; rw [trill]; exact hh
    have hL i:L i*star (L i)=1:= (license hh i).2 -- name
    rw [he]; change E=L i*(star (L i)*E*L j)*star (L j); simp only [Matrix.mul_assoc,hL,Matrix.mul_one]; rw [← Matrix.mul_assoc,hL,Matrix.one_mul] -- order simplification
lemma significance (Γ:Silo c)(h:Torch Γ)(s:Strut c)(g:Site c→ℂ)(W:Spike)(hh:Warrant s g W)(V: Grid c)(q:Tick c): pairQ Γ q (sky s V)=haze s W g *pairQ Γ (wheelS s q) V*star (haze s W g):=by
   apply Sway.whist; intro i j; unfold pairQ haze Revolve.hues; rw [pairBl,cell_ride_right,cell_ride_left,pairBl]; split
   next hx=> rw [motion Γ h s g W hh V q,trill]; obtain ⟨rfl,rfl⟩:=hx; rw [if_pos (by constructor <;> rfl)]; rfl
   next hx=> rw [trill]; change 0 = _ * (ite (act s i=act s q.1 ∧ act s j=act s q.2.1) _ _) *_; rw [if_neg (show ¬(act s i= _ ∧ act s j=_) from fun hv=>hx ⟨(act s).injective hv.1,(act s).injective hv.2⟩),mul_zero,zero_mul]
lemma dearth (Γ:Silo c)(h:Torch Γ)(N:ℕ)(s:Strut c)(g:Site c→ℂ)(W:Spike)(hh:Warrant s g W)(V:Grid c)(q:Tick c): Diode N s W g ((sealG Γ N).view q (sky s V))=(sealG Γ N).view (wheelS s q) V:=by
   apply rayTrade (Lat.copies N (haze s W g)) (copies_unitary _ _ (trail hh))
   have hp:(wheelS s (flopT q))=flopT (wheelS s q):=rfl
   rw [← copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg; unfold gleam; rw [significance Γ h s g W hh,significance Γ h s g W hh,hp,Matrix.mul_smul, Matrix.smul_mul,Matrix.mul_add, Matrix.add_mul]
variable {Γ:Silo c}{A:BankP c}{U: St c}
lemma chargeG {b:ℝ} (hp:Run.Pack id id η b k U r Γ A)(q:Tick c)(V:Grid c)(z:Frame c):pairQ Γ q (gauge z V)= siteRot z*pairQ Γ q V*star (siteRot z):=by
    apply Sway.whist; intro i j; rw [pairQ,pairBl]; unfold siteRot; rw [cell_ride_right,cell_ride_left,Equiv.refl_apply,Equiv.refl_apply,pairQ,pairBl]; split; next hx=> obtain ⟨rfl,rfl⟩:=hx; exact (hp.crop ..).2.2.2.2.2 ..
    next _=> rw [Matrix.mul_zero,zero_mul]
-- any price eliminator
lemma proofC {b:ℝ} (hp:Run.Pack id id η b k U r Γ A)(V:Grid c)(i:Tick c)(z:Frame c): fareP Γ i (gauge z V)=touch (colour (z i.1))*fareP Γ i V*star (touch (colour (z i.2.1))):=(hp.crop ..).2.2.2.2.2 ..
lemma glossy {b:ℝ} (hp:Run.Pack id id η b k U r Γ A)(h:Torch Γ)(N:ℕ): Crossing (sealG Γ N):=by
    refine ⟨⟨fun i V z=> ?_,fun i V=> form_fit _ N,fun i V=> dusted c N _ ?_⟩,fun s k g hh=> ⟨wheelS s,wheeled2 s k g hh⟩⟩
    · let B:=siteRot z; have hh (x:Tick c): pairQ Γ x (gauge z V)=B*pairQ Γ x V*star B:= chargeG hp ..
      apply congr_arg Subtype.val (Port.rayTrade (Lat.copies N B) (copies_unitary _ _ (siteRot_u z)) (gleam Γ (gauge z V) i) (gleam Γ V i) ?_); rw [←copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg; unfold gleam; rw [hh,hh]; simp only [Matrix.mul_smul, Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul]
    exact foldedS _ _ _ (fold_cell Γ h (flopT i) V) (fold_cell Γ h i V)
where
   wheeled2 (s:Strut c)(k:Spike)(g:Site c→ℂ)(hv: Warrant s g k)(i): dispatch (wheelS s i)=rotateL (dispatch i) s ∧∀ V,Diode N s k g ((sealG Γ N).view i (sky s V))=(sealG Γ N).view (wheelS s i) V:=⟨wheeled s i,fun _=>dearth Γ h N s g k hv _ _⟩
end YM.QCD.Entr
