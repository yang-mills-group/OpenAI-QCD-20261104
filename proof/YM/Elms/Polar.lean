import YM.Elms.Glass
import YM.Massive.Finite.Masks
/-! # Move by any gauge. locality of Homes. Depth-ready.C. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Civic
open QCD.Kites PrismD
local notation "τ"=> su.probHaar
variable (g:Frame n)
lemma ferment (p:Frame n): P.D (Lattice.gauge p U) = Lat.rotates 6 p *P.D U * star (Lat.rotates 6 p):=by
    let f: Lat.Cut n 6:=⟨P.β,P.t,0⟩; rw [Onsite.unmasked,Onsite.unmasked]; rw [show copies _ _= _ from rfl]; let X:=Lat.rotates 6 p; change f.ferm _+Onsite.offset _ _= X * (f.ferm _+_)*star X; rw [mul_add,add_mul,site_op,←Onsite.rotated _ _ p,Matrix.mul_assoc (Onsite.offset _ _),(rotates_law 6 p).2,mul_one]
lemma worldD : P.density U= slots 6 g (P.density (Lattice.gauge g U)):=by
   simp only [Regulator.density_apply,map_smul,bare_gauge]; unfold slots; rw [gauss_map,Matrix.transpose_transpose,ferment,← Matrix.mul_assoc,← Matrix.mul_assoc,← Matrix.mul_assoc,(Lat.rotates_law 6 g).1,Matrix.one_mul,Matrix.mul_assoc,(Lat.rotates_law 6 g).1,Matrix.mul_one] -- order
lemma raw_revert (Y:Insertion n 6) : P.average (transform g Y)= P.average Y :=by
    suffices h:P.raw (transform g Y)=P.raw Y by simp [Regulator.average,h]
    let F(U:Grid n):= ber _ (P.density U* Y U); have hf : Continuous F:=continuous_ber.comp ((P.density).continuous.mul Y.continuous)
    have he(V:Grid n): ber _ (P.density V *transform g Y V)= F (Lattice.gauge g V):=by
       unfold F; rw [←no_jac 6 g (P.density (Lattice.gauge g V)*Y (Lattice.gauge g V)), map_mul (slots 6 g), ← worldD V]; rfl
    change (∫ U:Grid n, ber _ (P.density U*transform g Y U) ∂prior su n)=(∫ U,F U ∂prior su n); simp_rw [he]; have h:=prior_gauge g; nth_rw 2 [← h.map_eq]; rw [integral_map h.aemeasurable hf.aestronglyMeasurable]
-- floors includes arbitrary.
set_option maxHeartbeats 500000 in
lemma carapace {x:Insertion n 6}{S:Set (Site n)}(hh: Floors S x): Floors S (transform g x):=by
    obtain ⟨f,hf,hF,hx⟩:= hh
    let V:↥S→su.El:=g ∘ (Subtype.val)
    let Y:= (Lat.copies 6 (rides (Equiv.refl S) (fun x:↥S=>Lat.touch (Lat.colour (g x.val)))))
    let L:=adapter Y (star Y).transpose
    let M:= slots 6 g
    let J:=pass (setDay S (F:=6)); have h : M.comp J= J.comp L:=by
       have hu (y:↥S)(a:Dike)(q:Bool): L (lineT q (place y a))=∑ j:Dike,peggle q (clutch (g y)) a j • lineT q (place y j):=by
           cases q
           · change adapter _ _ (psi _) = _; rw [adapt_psi,placed_sum,sum_eq_single y]; unfold Y; simp_rw [placed,Equiv.refl_apply,if_true]; rfl
             · intro b _ hb; simp [Y,placed,hb.symm]
             simp
           change adapter _ _ (bar _) = _; rw [adapt_bar,placed_sum,sum_eq_single y]; unfold Y; simp_rw [Matrix.transpose_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,placed,Equiv.refl_apply,if_true]; rfl
           · intro b _ hb; simp [Y,Matrix.transpose_apply,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, placed,Ne.symm hb]
           simp
       have he(y:↥S)(a:Dike)(q:Bool): J (lineT q (place y a))=lineT q (place y.val a):=by cases q; exact pass_psi ..; exact pass_bar ..
       have hf (y:↥S)(a:Dike)(q:Bool): M (J (lineT q (place y a)))=J (L (lineT q (place y a))):=by rw [he,show M _=_ from tops q a g y.val,hu,map_sum]; simp_rw [map_smul,he]
       apply Grass.ext_atoms; rintro (⟨⟨y,a⟩,w⟩|⟨⟨y,a⟩,w⟩)
       · exact hf y (a,w) false
       exact hf y (a,w) true
    let Te (U:Grid n):= L (f (Lattice.gauge g U)); refine ⟨Te,L.toLinearMap.continuous_of_finiteDimensional.comp (hf.comp (Lat.gauge_c g)), fun U V hh=>congr_arg L (hF _ _ ?_),fun U=>?_⟩
    · intro i hi hp; dsimp only [Lattice.gauge]; rw [hh i hi hp]
    change M (x _)= J _; rw [hx]; exact DFunLike.congr_fun h _
lemma reminded(x y:Insertion n 6): Lat.transform g (x*y)= Lat.transform g x*Lat.transform g y:= ContinuousMap.ext (fun U=> map_mul (slots 6 g) _ _)
lemma twin (X Y:Insertion n 6): P.average (Lat.transform g X*Y)=P.average (X*Lat.transform g⁻¹ Y):=by
     rw [← raw_revert P g (X*_ ),reminded,flares,inv_mul_cancel, slots_one] -- flares order check `Lat.transform f` g.W.roata
section Dryness
-- actual finite null of transformed op. require `Far` set measured distinct from flags but references.Flex weights. 
def NullOn (x:Insertion n 6)(S:Set (Site n)): Prop:= ∀ y:Insertion n 6, Floors S y → P.average (x*y)=0
lemma NullOn.mulInvariant {x: Insertion n 6}{S:Set (Site n)}(h:NullOn P x S): NullOn P (Lat.transform g x) S:=fun y he=> (twin P g x y).trans (h _ (carapace g⁻¹ he))
lemma addJoin {x y : Insertion n 6}{S:Set (Site n)}(h:NullOn P x S)(hf:NullOn P y S): NullOn P (x+y) S:=by intro p hp; rw [add_mul,map_add,h p hp,hf p hp,add_zero]
lemma scJoin {x:Insertion n 6}{S:Set (Site n)} (h:NullOn P x S) (c:ℂ): NullOn P (c • x) S:=by intro p hp; rw [_root_.smul_mul_assoc,map_smul,h p hp,smul_zero]
-- true Shears.Now.Mult use specifically formula erg. only need orbit membership of `X` realized for fixed P at n (dependent n's R), supplies from finite xt not need combined global.Hh.S (Orbit.add)
lemma Fins.addR {x y:Drape}(h:Fins x)(hx:Fins y): Fins (x+y):= Fins.of_span (Submodule.FG.sup h hx) (fun g=>by rw [map_add]; exact Submodule.add_mem _ (Submodule.mem_sup_left (outsideA x g)) (Submodule.mem_sup_right (outsideA y g)))
lemma Fins.scaleR {x:Drape}(h:Fins x) (a: ℂ):Fins (a • x):= Fins.of_span h (fun g=>by rw [map_smul]; exact Submodule.smul_mem _ _ (outsideA x _))
def lowerZ (S:Set (Site n)) (o:Cover) : Submodule ℂ Drape where
    carrier := {x| NullOn P (x n o) S}
    zero_mem' :=by intro y _; simp
    add_mem' :=by intro x y hx hy; exact addJoin P hx hy
    smul_mem' :=by intro c x hx; exact scJoin P hx c
lemma stillborn {X Y:Drape}(h:Shears X Y)(hp:Fins X) {S:Set (Site n)}(o:Cover)(hh:NullOn P (X n o) S): NullOn P (Y n o) S:=by
     have hv : OrbitW X ≤ lowerZ P S o:=by
         apply Submodule.span_le.mpr; rintro F ⟨g,rfl⟩; exact NullOn.mulInvariant P (gways g n) hh
     exact hv (h.in_spin hp)
end Dryness
end Civic
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Civic.stillborn
