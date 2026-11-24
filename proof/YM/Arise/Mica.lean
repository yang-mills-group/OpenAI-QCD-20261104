import YM.Arise.Tuck
/-! # all signed caps. compositional reach on probe slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge}
variable (s t: Signed)(x y:Cover)(a b:Axis)(p:PlaqAxes)(U:CoverConfig G)
variable (z:Cover) (l: List Axis)
lemma stake_join : (stake s x).comp (stake t y)=stake (s*t) (s.act y+x):=by
     apply LinearMap.ext; intro X; induction X using Finsupp.induction_linear with
     | zero=>simp
     | add i j h hp=> rw [map_add,map_add,h,hp]
     | single i a=> simp [stake,Signed.act_mul,Finsupp.smul_single',add_assoc]
lemma dent_join : dent (s*t) a=s.act (dent t a)+dent s (t.perm a):=by
     by_cases hf:s.flip (t.perm a)=true <;> by_cases h:t.flip a=true <;> simp [dent,hf,h,sst]
lemma bend_join : bend (s*t) p=s.act (bend t p)+bend s (took t p):=by
     unfold bend; rw [dent_join,dent_join, Signed.act_add]; unfold took tw; split <;> dsimp only <;> abel
lemma node_join (W:Rhythm): came (flux s (took t p) (flux t p W))= came (flux (s*t) p W):=by
    rw [live_power, live_power,live_power]; rw [bend_join, ← LinearMap.comp_apply, stake_join]
variable {H:Type*}[Fintype H][Nonempty H]
lemma Rocky.mean (p:Option PlaqAxes)(l:List Axis)(n:ℕ)(X:H→Parc)(h:∀ i,Rocky p l n (X i)):Rocky p l n ((Fintype.card H:ℝ)⁻¹ •∑ i,X i):=by
   let a:ℝ:=(Fintype.card H); have hp:0<a:=Nat.cast_pos.mpr Fintype.card_pos; let Y:=strike l 0; have he:a⁻¹ • ∑ _i:H,Y=Y:=by simp only [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,show a⁻¹ * ↑(Fintype.card H)=1 from inv_mul_cancel₀ hp.ne',one_smul]
   refine ⟨?_,?_⟩
   · change a⁻¹ • _- Y ∈_; rw [← he,← smul_sub,←sum_sub_distrib]; exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=> (h i).rest)
   intro k hp he; change stares p k _=0; rw [map_smul,map_sum,sum_eq_zero (fun i _=> (show stares p k (X i)=0 from (h i).stops _ hp he)), smul_zero]
noncomputable def song (n:ℕ)(l:List Axis)(p:Option PlaqAxes): Rhythm:= onde (Classical.choose (chooses p l n))
lemma soundR (l:List Axis)(p:Option PlaqAxes)(n:ℕ): Rocky p l n (came (song n l p)):=by rw [song,loads]; exact Classical.choose_spec (chooses p l n)
noncomputable def Vapors (s: Signed)(p:PlaqAxes)(l:List Axis)(X:Rhythm): Rhythm:=vane s l • flux s p X -- char derivative, plate sign outside.P. Reflection optic powers.Y
lemma ties(n:ℕ)(p:PlaqAxes)(X:Rhythm)(h:Rocky (some p) l n (came X))(hL:l.length≤n): Rocky (some (took s p)) (sways s l) n (came (Vapors s p l X)):=by unfold Vapors; rw [map_smul,live_power]; exact earned s (came X) (some p) l h hL
noncomputable def ant (p:PlaqAxes)(l:List Axis)(n:ℕ):= let x:= took s⁻¹ p; let y:= sways s⁻¹ l; Vapors s x y (song n y (some x))
noncomputable def chore(n:ℕ)(l:List Axis)(p:PlaqAxes): Rhythm:= (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,ant s p l n
lemma per_goal (p:PlaqAxes)(hL:l.length ≤ n): Rocky (some p) l n (came (chore n l p)):=by
     rw [chore,map_smul,map_sum]; refine Rocky.mean _ _ _ _ fun i=>?_ ; have ht:= ties i _ n _ (song n (sways i⁻¹ l) (some (took i⁻¹ p))) (soundR ..) ((sways_len i⁻¹ l).trans_le hL); rwa [← took_mul,← sways_mul, mul_inv_cancel,sways_id, took_start] at ht
noncomputable def petal := vane s l *glyphO s p -- multiplicative orientation.
lemma stain : petal (s*t) p l=petal s (took t p) (sways t l)*petal t p l:=by unfold petal; rw [glyph_mul,vane_mul]; ring
lemma still : petal s p l*petal s p l=1:=by unfold petal; rw [mul_mul_mul_comm,vane_sq,glyph_pin, mul_one]
lemma sights : paints (took s p) U (chore n (sways s l) (took s p))=petal s p l • paints p (pull s 0 U) (chore n l p):=by
     let Y(i:Signed):=took i⁻¹ p; let L(i:Signed):=sways i⁻¹ l
     have hp(i:Signed): paints (took s p) U (ant (s*i) (took s p) (sways s l) n)=petal s p l • paints p (pull s 0 U) (ant i p l n):=by
        let a:= Y i; let y:= L i; let m:= s*i
        have ht: took i a=p:=by unfold a Y; rw [← took_mul,mul_inv_cancel,took_start]
        have hl: sways i y=l:=by unfold y L; rw [← sways_mul,mul_inv_cancel,sways_id]
        have he:m⁻¹ = i⁻¹*s⁻¹:=mul_inv_rev ..
        have h1: took m⁻¹ (took s p)=a:=by rw [← took_mul,he,mul_assoc,inv_mul_cancel,mul_one]
        have h2: sways m⁻¹ (sways s l)=y:=by rw [← sways_mul,he,mul_assoc,inv_mul_cancel,mul_one]
        let H:=song n y (some a)
        have hu: paints (took s p) U (ant m (took s p) (sways s l) n)=petal m a y • paints a (pull m 0 U) H:=by unfold ant; dsimp only; rw [h1,h2, Vapors,map_smul, show took s p=took m a from Eq.symm (by unfold m; rw [took_mul,ht]), mints,petal, smul_smul]
        rw [hu]; change _= _ • paints p _ (Vapors i a y H); unfold Vapors; rw [map_smul,show paints p _ (flux i a H)=glyphO i a • paints a (pull m 0 U) H from (by rw [show p=took i a from ht.symm,mints,pull_pull]; simp [affine,m]),show petal m a y =petal s p l*petal i a y from by unfold m; rw [stain,ht,hl],mul_smul,show petal i a y=vane i y*glyphO i a from rfl,mul_smul]
     rw [chore,map_smul,map_sum, ← Equiv.sum_comp (Equiv.mulLeft s),chore,map_smul, map_sum,smul_comm (petal s p l)]
     conv_rhs=> rw [smul_sum]
     exact congr_arg ((Fintype.card Signed:ℝ)⁻¹ • ·) (sum_congr rfl fun i _=>hp i) -- smul_sum order
lemma grouped : came (chore n (sways s l) (took s p))=vane s l • stake s (bend s p) (came (chore n l p)):=by
     let Y(i:Signed):=took i⁻¹ p; let L(i:Signed):= sways i⁻¹ l
     have hp(i:Signed): came (ant (s*i) (took s p) (sways s l) n)=vane s l • stake s (bend s p) (came (ant i p l n)):=by
        let a:= Y i; let y:= L i; let m:= s*i
        have ht: took i a=p:=by unfold a Y; rw [← took_mul,mul_inv_cancel,took_start]
        have hl: sways i y=l:=by unfold y L; rw [← sways_mul,mul_inv_cancel,sways_id]
        have he:m⁻¹ = i⁻¹*s⁻¹:=mul_inv_rev ..
        have h1: took m⁻¹ (took s p)=a:=by rw [← took_mul,he,mul_assoc,inv_mul_cancel,mul_one]
        have h2: sways m⁻¹ (sways s l)=y:=by rw [← sways_mul,he,mul_assoc,inv_mul_cancel,mul_one]
        change came (ant m _ _ n)=vane s l • stake _ _ (came (Vapors i a y _)); unfold ant; dsimp only; rw [h1,h2]; unfold Vapors; rw [map_smul,map_smul,← node_join s i a,live_power,ht,map_smul,vane_mul,hl,mul_smul] -- m let
     let V:=(Fintype.card Signed:ℝ)⁻¹; rw [chore,map_smul,map_sum,← Equiv.sum_comp (Equiv.mulLeft s),chore,map_smul,map_smul,map_sum,map_sum]
     conv_rhs=>rw [smul_comm (vane s l) V (∑ i:Signed, stake s (bend s p) (came (ant i p l n))), smul_sum]
     exact congr_arg (V • ·) (sum_congr rfl fun i _=>hp i)
end YM.Arise
#print axioms YM.Arise.sights
#print axioms YM.Arise.grouped
