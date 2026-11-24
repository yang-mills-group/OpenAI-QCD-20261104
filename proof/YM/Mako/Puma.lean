import YM.Mako.Tall
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Polynomial
open scoped Topology BigOperators Classical
open Vern
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
local notation "ι0"=> Fin (Module.finrank ℂ W)
variable {H E F: Module.End ℂ W} (v:W)
structure Links (H E F:Module.End ℂ W) :Prop where
     he : H*E-E*H=(2:ℂ) • E
     hf : H*F-F*H= (-2:ℂ) • F
     ef : E*F-F*E= H
namespace Links
variable (h:Links H E F)
include h
lemma refl : Links (-H) F E:=by
    refine ⟨?_,?_,?_⟩
    · rw [neg_mul,mul_neg,show (-(H*F))- -(F*H) = -(H*F-F*H) from by abel,h.hf,neg_smul,neg_neg]
    · rw[neg_mul,mul_neg,neg_smul, ←h.he]; abel
    rw[←h.ef]; abel
lemma etch (r:ℂ)(x:W)(hx: H x= r • x): H (E x)=(r+2) • E x:=by
     have hv:H (E x)-E (H x)= (2:ℂ) • E x:=DFunLike.congr_fun h.he x; rw [hx,map_smul,sub_eq_iff_eq_add] at hv; rw [hv,add_comm,←add_smul]
lemma eft (r:ℂ)(x:W)(hx: H x=r • x)(n:ℕ): H ((E^n) x)=(r+2*(n:ℂ)) • ((E^n) x):=by
    induction n with
    | zero=> simp[hx]
    | succ n ih=> rw [pow_succ',Module.End.mul_apply,h.etch _ _ ih]; congr 1; push_cast; ring
lemma fur (r:ℂ)(x:W)(hx: H x=r • x)(n:ℕ):H ((F^n) x)=(r-2*(n:ℂ)) • ((F^n) x):=by
     have hp: (-H) x=(-r) • x:=by simp [hx]
     have ht:= h.refl.eft _ _ hp n; change -_= _ at ht; rw [neg_eq_iff_eq_neg,← neg_smul] at ht; rw[ht]; congr 1; ring
-- nil exponent existence via finite eigenspace support
lemma silenced (hc:Clear H): ∃ N:ℕ,E^(N+1)=0:=by
     obtain ⟨B,a,ha⟩:= hc; have hA(i j:ι0): ∀ᶠ N:ℕ in atTop,a j ≠ a i+2*(N+1:ℕ):=by
            let b:= (((a j).re - (a i).re)/2); obtain ⟨z,hz⟩:=exists_nat_gt b; filter_upwards [eventually_ge_atTop z] with N hN hh; apply not_le_of_gt hz; have hz': (z:ℝ)≤ N:=by exact_mod_cast hN
            have hp:= congr_arg Complex.re hh; norm_num [Complex.mul_re] at hp; unfold b; linarith
     obtain ⟨N,hN⟩:= (eventually_all.mpr (fun i=> eventually_all.mpr (hA i))).exists
     refine ⟨N,B.ext fun i=>?_⟩; let x:=(E^(N+1)) (B i); have he:= h.eft _ _ (ha i) (N+1); change x=0; apply B.equivFun.injective; funext j; change B.coord j x=B.coord j 0; rw [map_zero]; by_contra hv; apply hN i j; apply mul_right_cancel₀ hv; rw[← studs H B a ha,show H x=_ from he,map_smul]; rfl
lemma undone (hc:Clear H): ∃ N:ℕ,F^(N+1)=0:=by
    apply h.refl.silenced; obtain ⟨B,a,ha⟩:=hc; exact ⟨B,-a,fun i=>by simp[ha]⟩
-- E F^n = F^n E + n(λ-n+1)F^{n-1}; n=m+1
lemma funne (r:ℂ)(x:W)(hx: H x=r • x) (n:ℕ): E ((F^(n+1)) x)= (F^(n+1)) (E x) + (((n:ℂ)+1)*(r-(n:ℂ))) • ((F^n) x):=by
     have hm (y:W): E (F y)= F (E y)+H y:=by
             have h:E (F y)-F (E y)=H y:= DFunLike.congr_fun h.ef y; rw [sub_eq_iff_eq_add] at h; rw[h,add_comm]
     induction n with
     | zero=> simp[hm,hx]
     | succ n ih=> rw [pow_succ' F (n+1),Module.End.mul_apply, hm, h.fur r x hx, ih,map_add,map_smul,←Module.End.mul_apply F (F ^ n),←pow_succ' F]; rw [add_assoc,← add_smul]; congr 2; push_cast; ring
-- E^n F = F E^n + n(λ+n−1) E^{n-1}
lemma enn (r:ℂ)(x:W)(hx:H x=r • x)(n:ℕ): (E^(n+1)) (F x)= F ((E^(n+1)) x)+(((n:ℂ)+1)*(r+(n:ℂ))) • ((E^n) x):=by
     have he:= h.refl.funne (-r) x (by simp [hx]) n; rw [he] -- combine
     rw [add_assoc,← add_smul,show ((n:ℂ)+1)*(-r-n)+(n+1)*(r+n)=0 by ring,zero_smul, add_zero]
-- E kills and H zero ⇒ F kills
lemma f_kill (hc:Clear H)(x:W)(he:E x=0)(hv:H x=0):F x=0:=by
     obtain ⟨N,hN⟩:= h.undone hc; have hx(q:ℕ)(hv':(F^(q+1)) x=0): F x=0:=by
          induction q with
          | zero=>simpa using hv'
          | succ n ih=>
                have hs:= h.funne 0 x (by rw[hv,zero_smul]) (n+1); rw [hv',map_zero,he,map_zero,zero_add] at hs; apply ih; apply (smul_eq_zero.mp hs.symm).resolve_left; rw [zero_sub]; refine mul_ne_zero ?_ (neg_ne_zero.mpr ?_)
                · exact_mod_cast Nat.succ_ne_zero (n+1)
                exact_mod_cast Nat.succ_ne_zero n
     exact hx N (DFunLike.congr_fun hN x)
end Links
end YM.Mako
#print axioms YM.Mako.Links.enn
#print axioms YM.Mako.Links.f_kill
