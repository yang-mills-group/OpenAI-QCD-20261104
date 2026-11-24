import YM.Mako.Puma
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Polynomial Module
open scoped Topology BigOperators Classical
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
local notation "ι0"=> Fin (Module.finrank ℂ W)
variable {H E F: Module.End ℂ W}(x y:W)(B:Basis ι0 ℂ W)(a:ι0→ℂ) (h:Links H E F) (hc:Clear H)
-- Lagrange projector for Cartan weight 0
structure Lace (H: Module.End ℂ W) where
    poly: Polynomial ℂ
    root : poly.eval 0=1
    zero :∀ v:W, H ((aeval H poly) v)=0
    smite : ∀ (b:ℂ)(v:W), H v=b • v → b≠0 → (aeval H poly) v=0
lemma pay {f:Module.End ℂ W}{x:W}{b:ℂ}(P:Polynomial ℂ)(h:f x=b • x) : aeval f P x=P.eval b • x :=by
    by_cases hx:x=0; · subst x; simp
    exact End.aeval_apply_of_hasEigenvector (show f.HasEigenvector b x from ⟨End.mem_eigenspace_iff.mpr h,hx⟩)
namespace Lace
lemma fixes(p:Lace H)(h:H x=0) : aeval H p.poly x=x:=by rw [pay p.poly (show H x=(0:ℂ) • x from by rw[zero_smul,h]),p.root,one_smul]
lemma earns (hc:Clear H): Nonempty (Lace H):=by
     obtain ⟨B,a,ha⟩:=hc; let s:Finset ℂ:= (Finset.univ.image a).erase 0; let P:= ∏ μ∈s,(1-C μ⁻¹*X)
     have h0:P.eval 0=1:=by simp [P,Polynomial.eval_prod]
     have he(v:W)(b:ℂ)(h:H v=b • v)(hx:b≠0) : (aeval H P) v=0:=by
          by_cases hu:v=0; · subst v; exact map_zero _
          have hp :∃ i:ι0, B.coord i v≠0:=by by_contra! hv; apply hu; rw[←B.sum_repr v]; change ∑ i:ι0,B.coord i v • B i=_; simp [hv]
          obtain ⟨i,hi⟩:= hp; have hs:a i=b:= mul_right_cancel₀ hi (by rw [← studs H B a ha,h,map_smul]; rfl)
          rw [pay P h,show P.eval b=0 from ?_,zero_smul]; unfold P; rw[Polynomial.eval_prod]; apply Finset.prod_eq_zero (i:=b); · exact Finset.mem_erase.mpr ⟨hx, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hs⟩⟩
          simp [hx]
     refine ⟨⟨P,h0,fun x=>?_,fun b v h hx=> he v b h hx⟩⟩; change (H*aeval H P) x=0; rw [show H*aeval H P=0 from ?_]; rfl
     refine B.ext fun i=>?_; by_cases h:a i=0; · simp [pay P (ha i),h,h0,ha i]
     change H ((aeval H P) (B i))=0; rw [he (B i) (a i) (ha i) h,map_zero]
noncomputable def credit (hc:Clear H): Lace H:= Classical.choice (earns hc)
end Lace
-- coefficient recursion, finite telescope, independently check both range and image
noncomputable def fee : ℕ→ℂ
     | 0=>1
     | n+1=> -(fee n) / (((n:ℂ)+1)*((n:ℂ)+2))
lemma account (n:ℕ): fee (n+1)*((n:ℂ)+1)*(n+2)= -fee n:=by
     have h:(n:ℂ)+1≠0:=by exact_mod_cast Nat.succ_ne_zero n
     have hp:(n:ℂ)+2≠0:=by exact_mod_cast Nat.succ_ne_zero (n+1)
     rw [fee,mul_assoc,div_mul_cancel₀ _ (mul_ne_zero h hp)]
noncomputable def pledge (E F:Module.End ℂ W): ℕ → Module.End ℂ W
    | 0=> 1
    | n+1=> pledge E F n+ fee (n+1) • (F^(n+1)*E^(n+1))
namespace Links
include h
lemma diving (x:W)(hx:H x=0)(j:ℕ): H (pledge E F j x)=0:=by
     induction j with
     | zero=> simp [pledge,hx]
     | succ j ih=> rw[pledge,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,map_add,map_smul,ih, h.fur _ _ (h.eft 0 x (by rw[zero_smul,hx]) (j+1)),zero_add (2*(↑(j+1):ℂ)),sub_self,zero_smul,smul_zero,add_zero]
lemma cat(x:W)(hx:H x=0)(j:ℕ): E (pledge E F j x)= fee j • (F^j) ((E^(j+1)) x):=by
     induction j with
     | zero=> simp [pledge,fee]
     | succ j ih=>
         rw[pledge,LinearMap.add_apply,map_add,LinearMap.smul_apply,map_smul,ih] -- map_smul prior simp smul_apply
         -- telescope
         rw[Module.End.mul_apply,h.funne _ _ (h.eft 0 x (by rw[zero_smul,hx]) (j+1)) j]; rw[←Module.End.mul_apply E (E^(j+1)),← pow_succ', smul_add,smul_smul];
         rw [show fee (j+1) * (((j:ℂ)+1)*(0+2*((j+1:ℕ):ℂ)-j))=-fee j from ?_,neg_smul]; abel
         rw [←account j]; push_cast; ring
lemma cour(x:W)(hx:H x=(2:ℂ) • x)(j:ℕ): pledge E F j (F x)= fee j • (F^(j+1)) ((E^j) x):=by
     induction j with
     | zero=> simp [pledge,fee]
     | succ j ih=>
           rw[pledge,LinearMap.add_apply,LinearMap.smul_apply, ih, Module.End.mul_apply,h.enn _ _ hx,map_add,map_smul,←Module.End.mul_apply (F^(j+1)) F, ←pow_succ,smul_add,smul_smul,←mul_assoc,add_comm (2:ℂ), account j, neg_smul]; abel
-- image E also killed
lemma covered (hc:Clear H) (x:W)(hx:H x=(-2:ℂ) • x):∃ v:W,H v=0∧x=F v:=by
     obtain ⟨N,hN⟩:= h.undone hc
     suffices ht:(F^(N+1)) x=0→ ∃ v:W,H v=0∧x=F v from ht (DFunLike.congr_fun hN x)
     generalize hn:N+1=k; clear hn; induction k generalizing x with
     | zero=> intro he; refine ⟨0,map_zero _,?_⟩; simpa using he
     | succ n ih=>
          intro he; let c:ℂ:= ((n:ℂ)+1)*(-(2:ℂ)-n); have hp: c≠0:=by
                 unfold c; apply mul_ne_zero; · exact_mod_cast Nat.succ_ne_zero n
                 rw [show (-(2:ℂ)-n) = - ((n:ℂ)+2) from by ring]; exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero (n+1))
          have hE:H (E x)= (0:ℂ) • (E x):=by rw[h.etch _ _ hx]; norm_num
          have hX: H (F (E x))=(-2:ℂ) • F (E x):=by simpa using! h.fur _ _ hE 1 -- issue hx simpl
          have ht:= h.funne _ _ hx n; rw[he,map_zero,pow_succ F n,Module.End.mul_apply] at ht
          let y:=x+c⁻¹ • F (E x)
          obtain ⟨v,hv,hY⟩:= ih y (by unfold y; rw[map_add,map_smul,hx,hX,smul_comm c⁻¹,smul_add]) (by
                unfold y; rw[map_add,map_smul,show (F^n) (F (E x))= -(c • (F^n) x) from eq_neg_of_add_eq_zero_left ht.symm,smul_neg, inv_smul_smul₀ hp,add_neg_cancel])
          refine ⟨v-c⁻¹ • E x,by rw [map_sub,map_smul,hv,hE,zero_smul,smul_zero, sub_self],?_⟩; rw [map_sub,map_smul,←hY]; unfold y; rw[add_sub_cancel_right]
end Links
end YM.Mako
#print axioms YM.Mako.Links.cat
#print axioms YM.Mako.Links.cour
#print axioms YM.Mako.Links.covered
#print axioms YM.Mako.Lace.credit
