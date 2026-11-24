import YM.Mako.Jaunt
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
open Ortho (plane Skew)
open Org
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ: EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
include H J JQ B R
lemma loans(d:ℕ)(hd:8 ≤d):∃ F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d),Flyers A d hd T F:=by
      obtain ⟨f,hf,hA⟩:= mints J H JQ B R hd; exact ⟨f 0,hf 0⟩
include S
lemma hauls (p:Skew)(t:ℝ)(x:K.W): A.jet p (ρ (oathU p t) x)= ρ (oathU p t) (A.jet p x):=by
     obtain ⟨d,hd,hx⟩:= S.toll JQ.h (loans J H JQ B R) x; obtain ⟨F,hF⟩:= loans J H JQ B R d hd; exact locks J H JQ B R S hd hd F F hF hF _ (fun i hi=>A.landed _ hd _ i hi) p (Commute.refl _) x hx t
variable (a b:Axis)(h:a≠b)
omit H J JQ B R S
include h
@[simp]lemma fairHalf : EuPin.Lifts (oathU (plane a b) Real.pi) (Signed.mirror a*Signed.mirror b):= Eq.trans ((tour _).2.2 _) ((SpinPlane.half a b h).trans (map_mul Signed.inclusionO ..).symm) -- include h
include H J JQ B R S
set_option quotPrecheck false
local notation "U"=> oathU (plane a b) Real.pi
lemma nug(i:Axis)(he:i=a∨i=b)(x:K.W): ρ (oathU (plane a b) Real.pi) (K.arc i x)= -(K.arc i (ρ (oathU (plane a b) Real.pi) x)):=by
      let s:=Signed.mirror a*Signed.mirror b; have hx: EuPin.Lifts U s:= fairHalf a b h; rw[S.acts JQ.h (loans J H JQ B R) _ _ hx,pith H JQ.h x i s U hx,show s.perm i=i from rfl,show signT s i=-1 from ?_,Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul]; rcases he with rfl|rfl <;> simp [signT,s,Signed.mirror, h,Ne.symm h] -- xor
lemma nog(x:K.W): ρ U (B.edge a x)= -B.edge a (ρ U x):=by
      rw [← limb J H JQ B R a b h]; change ρ U (A.jet _ (K.arc _ x)- K.arc _ (A.jet _ x))= -(_ - _); rw[map_sub,←hauls J H JQ B R S, nug J H JQ B R S a b h b (Or.inr rfl),map_neg,nug J H JQ B R S a b h b (Or.inr rfl), ←hauls J H JQ B R S]; abel
lemma lit(x:K.W):K.arc a x=B.edge a x:=by
      obtain ⟨d,hd,hx⟩:= S.toll JQ.h (loans J H JQ B R) x; have hh:8 ≤ d+2:=by omega
      obtain ⟨F,hF⟩:=loans J H JQ B R d hd; obtain ⟨Y,hY⟩:=loans J H JQ B R (d+2) hh; have hv:= locks J H JQ B R S hd hh F Y hF hY (K.arc a-B.edge a) (fun z h=> (K.level (d+2)).sub_mem (JQ.h.graded a d z h) (hems J H JQ B R 0 d hd a z h)) (plane a b) (connect J H JQ B R a b a) x hx Real.pi -- shadows with h bool
      let y:= K.arc a (ρ U x); let z:=B.edge a (ρ U x); have hax:=nug J H JQ B R S a b h a (Or.inl rfl) x; have he:= nog J H JQ B R S a b h x
      have hh:y=z:=by
           change y-z=ρ U (K.arc a x-B.edge a x) at hv
           rw [map_sub,hax,he] at hv; apply sub_eq_zero.mp; have ht:(2:ℂ) • (y-z)=0:=by
                 have hp:y-z= -(y-z):= Eq.trans hv (by unfold y z; abel)
                 rw[two_smul]; conv_lhs=>rhs; rw [hp]
                 abel
           exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
      exact (ρ U).injective (hax.trans ((congr_arg Neg.neg hh).trans he.symm))
omit h
lemma wins: K.arc=B.edge:=by
      funext a; obtain ⟨i,h⟩:= exists_ne a; exact LinearMap.ext (lit J H JQ B R S a i (Ne.symm h))
lemma valiant(g:Ortho.Skew)(a:Axis)(v:K.W): A.jet g (K.arc a v)= K.arc a (A.jet g v) + ∑ b:Axis,(g.val b a:ℂ) • K.arc b v:=by
      have ht:= B.sparks H JQ.h A v a g; rw[← wins J H JQ B R S,sub_eq_iff_eq_add,add_comm] at ht; exact ht
-- inspires OFF line
end YM.Mako
#print axioms YM.Mako.valiant
