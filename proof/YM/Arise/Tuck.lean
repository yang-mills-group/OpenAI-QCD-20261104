import YM.Arise.Pear
import YM.Work.G06.TurnSlot
/-! # Cash from oriented stencil aperture to path packs. Keeps signed affection exactly on values. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge}
variable (s t: Signed)(x y:Cover)(a b:Axis)(p:PlaqAxes) (w:Walk)
variable (z:Cover) (l: List Axis)
lemma hale_last (x: Cover): stop (s.act x) (w.map (·.rotate s))=s.act (stop x w):=by induction w generalizing x with|nil=>rfl|cons a x ih=> rw [List.map_cons,stop,stop,Step.vec_rotate,←Signed.act_add, ih]
noncomputable def tap (w:Walk):= w.map (·.rotate s)
noncomputable def tune (i:Axis)(w:Walk):= if s.flip i then w++[negDir (s.perm i)] else w
lemma takes (a :Axis)(z:Cover) : stop z (tune s a w)=stop z w+dent s a:=by unfold tune dent; split<;> simp [stop_append,stop] -- simp false
noncomputable def lake (w:Walk) := tune s p.val.2 (tune s p.val.1 (tap s w))
lemma levels : stop (0:Cover) (lake s p w)=s.act (stop 0 w)+bend s p:=by
    unfold lake bend; rw [takes,takes,add_assoc]; exact congr_arg (·+_) (by unfold tap; simpa using hale_last s w (0:Cover)) -- hc ambiguous
variable (U:CoverConfig G)
lemma by_path (ha:a≠b): slanted w (posDir a) (posDir b) U=(if a<b then 1 else -1 : ℝ) • Slot.eval ⟨w,tw a b ha⟩ U:=by
    unfold tw; split; next h=> rw [one_smul]; rfl
    next h=> rw [neg_one_smul, slanted_swap w (posDir b)]; rfl -- layout
lemma takes_first (v:Lattice.Step): slanted w ((posDir a).rotate s) v U=hue s a • slanted (tune s a w) (posDir (s.perm a)) v U:=by
    by_cases h:s.flip a=true
    · rw [show (posDir a).rotate s=negDir (s.perm a) from (by simp [Step.rotate,posDir,negDir,h]),show hue s a=-1 from if_pos h,neg_one_smul,tune,if_pos h, ←slanted_next w,Step.rev_neg]; exact slanted_swap ..
    have hh:s.flip a=false:=Bool.eq_false_iff.2 h; rw [show (posDir a).rotate s=posDir (s.perm a) from (by simp [Step.rotate,posDir,h,hh]),hue,if_neg h,one_smul,tune,if_neg h]
lemma takes_next(v:Lattice.Step): slanted w v ((posDir a).rotate s) U=hue s a • slanted (tune s a w) v (posDir (s.perm a)) U:=by
    rw [slanted_swap w ((posDir a).rotate s),takes_first, slanted_swap _ v,smul_neg,neg_neg]
lemma earns_t : Slot.eval ⟨w,p⟩ (pull s 0 U)=glyphO s p • Slot.eval ⟨lake s p w, took s p⟩ U:=by rw [slot_pos, slanted_pull]; change slanted (tap s w) ((posDir p.val.1).rotate s) ((posDir p.val.2).rotate s) U=_; rw [takes_first,takes_next,by_path _ _ _ _ (s.perm.injective.ne p.property.ne),smul_smul,smul_smul]; dsimp only [lake,glyphO,took]; rw [mul_comm (hue s p.val.1*hue s p.val.2),← mul_assoc] -- maybe
section Parlance
abbrev Rhythm := (Walk→₀ ℝ)
variable (W:Rhythm)
noncomputable def hears {F:Type*}[AddCommMonoid F][Module ℝ F](f:Walk→F):Rhythm→ₗ[ℝ]F:= Finsupp.linearCombination ℝ f
noncomputable def came :Rhythm→ₗ[ℝ]Parc:= hears fun w=> Finsupp.single (stop 0 w) 1
noncomputable def onde : Parc→ₗ[ℝ] Rhythm:= Finsupp.linearCombination ℝ (fun p=>Finsupp.single (route 0 p 1) 1) -- norm Rhythm lacking; use lC.lin
lemma loads(X:Parc): came (onde X)=X:=by induction X using Finsupp.induction_linear with|zero=>simp|add a b h h'=> rw [map_add,map_add,h,h']|single i a=>simp [came,onde,hears,Finsupp.smul_single',sound,route_end]
lemma hearth (f:Cover→F): sound f (came W)= hears (f∘(stop (0:Cover))) W:=by induction W using Finsupp.induction_linear with|zero=>simp|add u v h hp=>rw [map_add,map_add,map_add,h,hp]|single i a=>simp [came,hears,Finsupp.smul_single',sound]
noncomputable def flux (s:Signed)(p:PlaqAxes) : Rhythm→ₗ[ℝ] Rhythm:= hears fun w=>Finsupp.single (lake s p w) 1
lemma live_power : came (flux s p W)=stake s (bend s p) (came W):=by induction W using Finsupp.induction_linear with|zero=>simp|add u v h hp=>rw [map_add,map_add,map_add,map_add,h,hp]|single i a=>simp [flux,hears,came,stake,levels]
noncomputable def paint {G:Gauge}(W:Rhythm)(p:PlaqAxes)(U:CoverConfig G): G.Color:=hears (fun w=> Slot.eval (G:=G) ⟨w,p⟩ U) W
noncomputable def paints {G:Gauge}(p:PlaqAxes)(U:CoverConfig G): Rhythm→ₗ[ℝ] G.Color:=hears (fun w=> Slot.eval (G:=G) ⟨w,p⟩ U)
lemma mints : paints (took s p) U (flux s p W)=glyphO s p • paints p (pull s 0 U) W:=by
    induction W using Finsupp.induction_linear with
    | zero=>simp
    | add u v h hp=> rw [map_add,map_add,map_add,h,hp,smul_add]
    | single i a=>simp only [flux,Finsupp.linearCombination_single,Finsupp.smul_single',paints,hears,mul_one,smul_eq_mul, earns_t]; rw [smul_comm (glyphO s p) a,smul_smul (glyphO s p) (glyphO s p),glyph_pin,one_smul]
end Parlance
end YM.Arise
