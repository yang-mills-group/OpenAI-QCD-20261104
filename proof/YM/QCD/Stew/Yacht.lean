import YM.QCD.Stew.Cauldron
/-! # affine moment columns. The compulsory frame HC and scalar phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
lemma gold_s (b:ℂ)(D: Bundle): gold (b • D)=b • gold D:=rfl
lemma shine_step (o:Site c)(i:Step)(h:4≤ c.val):shine o (o+i.vec)=glint 0 o i:=by
   rw [shore o (o+i.vec) [i]]; · simp [shimmer]
   rw [heel,lift_step ?_ h]; · simp only [Lattice.stop,zero_add,sub_self]; rw [show lift (0:Site c)=0 from ?_,zero_add]; ext; simp [lift]
   simp
lemma slide (o:Site c)(hn:4≤ c.val)(p:Step)(s:SampleX)(M:Spike): shape o (localX o M*leg (0:Site c) 1 p) s=mark o s o (o+p.vec) • M:=by
    unfold shape; let X:=localX o M*leg (0:Site c) 1 p
    have he (i j) (hi:o≠i∨ i+p.vec ≠ j): cell X i j=0:=by
       unfold X localX; rw [leg_day,ride_mul, board]; split
       next hh=>
          have hh: i+p.vec=j:=hh
          rw [if_neg (hi.resolve_right (not_not_intro hh)),zero_mul]
       next hh=> rfl
    have hp: touch (hitch 0 (1:Grid c) p o)=glint (0:Site c) o p • 1:=by unfold hitch; rw [show p.read (1:Grid c) o=1 from by simp [Step.read],show colour 1=1 from rfl]; exact (Matrix.kronecker_smul ..).trans (congr_arg _ touch_one)
    rw [sum_eq_single o]; rotate_left
    · intro i _ hi; refine sum_eq_zero fun j _=>?_ ; rw [he i j (.inl hi.symm),gold0, smul_zero]
    · simp
    rw [sum_eq_single (o+p.vec)]; rotate_left
    · intro j _ hi; rw [he _ _ (.inr hi.symm),gold0, smul_zero]
    · simp
    rw [shine_self,shine_step o p hn,localX,leg_day,ride_mul,board,Equiv.refl_trans]; simp only [Equiv.refl_apply]; rw [if_pos (show (Equiv.addRight (p.vec)) o=o+p.vec from rfl), if_true,hp, Matrix.mul_smul,mul_one,gold_s,leafy,one_mul, smul_smul,mul_right_comm,glint_sq,one_mul]
    -- solve
lemma Δ_right (o:Site c)(hn:4≤ c.val)(p:Axis)(X:Spike)(s:SampleX):shape o (entry o X (some (p,true)) 1) s=if s= some (p,true) then X else 0:=by
   change shape o (localX o X* delta 1 p) s=_; unfold delta; rw [Matrix.mul_smul,mul_sub,metallic, sub_eq_add_neg, solid,← neg_one_smul ℂ,metallic]; change (2:ℂ)⁻¹ • (shape o (_ * leg _ _ (posDir p)) s+ (-1:ℂ) • shape o (_* leg _ _ (negDir p)) s)=_
   rw [slide o hn,slide o hn]; rcases s with _|⟨i,b⟩
   · simp [mark]
   have he : lift ((0:Site c))=0:=by ext; simp [lift]
   cases b
   · simp [mark,lift]
   have hh (v:Step): mark o (some (i,true)) o (o+v.vec)= (((v.vec:Cover) i:ℤ):ℂ):=by change (↑(lift (o+v.vec-o) i):ℂ)=_; rw [lift_step (show 10* separation o o < c.val from by simp) hn, sub_self,he,zero_add]
   rw [hh,hh]; by_cases h:i=p
   · have hx : (2:ℂ)⁻¹ • (X+X)=X:=by rw [← two_smul ℂ, inv_smul_smul₀ (by norm_num)];
     simpa [h,neg_one_smul] using hx
   simp [h]
lemma both (o:Site c)(hn:4≤ c.val)(X:Spike)(s p:SampleX):shape o (entry o X p 1) s=if s=p then X else 0:=by
    rcases p with _|⟨a,_|_⟩
    · exact atO ..
    · let q:= some (a,true)
      rw [hero, show shape o (star _) s=star (shape o (entry o (star X) q 1) (invert s)) from (by simpa only [Stew.inv_inv] using chess o (entry o (star X) q 1) (invert s)),Δ_right o hn]; have he : invert s=some (a,true)↔s=some (a,false):=by cases s <;> simp [invert] <;> aesop
      simp only [he]; split <;> simp
    exact Δ_right o hn a X s
end YM.QCD.Stew
