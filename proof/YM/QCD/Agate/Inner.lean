import YM.QCD.Plum.Gist
import YM.QCD.Land.Refract
import YM.QCD.RP.Yard
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Plum Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
abbrev Paper (D:Lot)(F:ℕ):= Trace D→ Poly D F
variable {D S Z:Lot}
noncomputable def political (D:Lot)(F:ℕ):Subalgebra ℂ (Paper D F) where
    carrier:={x| Stays x ∧ ∀ (k:Town D)(U:Trace D),turnin k F (x (stain k U))=x U}
    algebraMap_mem' i:=by change Stays (fun _=> algebraMap _ _ i) ∧ _; exact ⟨stays continuous_const, fun k U=>AlgHom.commutes (turnin k F) i⟩
    add_mem' hx hy:=by
         obtain ⟨hx,hX⟩:=hx; obtain ⟨hy,hY⟩:=hy
         exact ⟨(hx.both hy).flows continuous_add,fun k U=> by simp only [Pi.add_apply,map_add,hX,hY]⟩
    mul_mem' hx hy:=by obtain ⟨hx,hX⟩:= hx; obtain ⟨hy,hY⟩:=hy; exact ⟨hx.mult hy,fun k U=> by simp only [Pi.mul_apply,map_mul,hX,hY]⟩
abbrev Grain (D:Lot) (F:ℕ):= political D F
noncomputable abbrev Malt (D:Lot)(F:ℕ):Type:= (political D F:Type)
lemma staysP (P:Malt D F): Stays P.val:=P.property.1
lemma yoke (P:Malt D F)(k:Town D)(U:Trace D): turnin k F (P.val (stain k U))=P.val U:=P.property.2 k U
-- Aperture extraction centered. works with any site shift
noncomputable def leap (p:Site c)(i:Cover): Site c:=wrap c i+p
noncomputable def strike (p:Site c)(k:Pipe D): Edge (Site c):=(leap p (inlet k).val,way k)
noncomputable def crest (p:Site c)(V:Grid c): Trace D:=fun i=> V (strike p i)
lemma crestC (p:Site c): Continuous (crest (D:=D) p):=by unfold crest; fun_prop
lemma leapS (p:Site c)(x:Cover)(a:Axis): leap p (x+step a)=leap p x+step a:=by unfold leap; rw [map_add,wrap_step]; abel
lemma drainH(p:Site c)(k:Pipe D): leap p (drain k).val=(strike p k).1+step (strike p k).2:=leapS ..
lemma crested (p:Site c)(h:Fits c D): Injective (strike p (D:=D)):=by
    intro i j e; apply coveredge_inj; have hv := congr_arg Prod.fst e; unfold strike leap at hv; dsimp only at hv; exact Prod.ext (h (inlet i).property (inlet j).property (add_right_cancel hv)) (congr_arg (fun i : Edge (Site c)=> i.2) e)
lemma atone (p:Site c)(U:Grid c): crest (D:=D) p U=inspects (expandAt p U):=rfl
lemma stainH (p:Site c)(k:Frame c) (U:Grid c): crest (D:=D) p (gauge k U)= stain (D:=D) (fun i=>k (leap p i.val)) (crest p U):=by funext i; unfold crest stain Lattice.gauge; rw [← drainH]; rfl
noncomputable def pens (p: Site c)(i:Pad D F): Modes c F:= ((leap p i.1.1.val,i.1.2),i.2)
noncomputable def jewel (p:Site c)(V:Paper D F) (U: Grid c):Fields c F := pass (pens p) (V (crest p U))
noncomputable def windows (D:Lot)(p:Site c):Set (Site c):=leap p '' D
lemma pensI (p:Site c)(h:Fits c D):Injective (pens p (D:=D) (F:=F)):=by
     intro i j e; refine Prod.ext (Prod.ext (Subtype.ext (h i.1.1.property j.1.1.property (add_right_cancel (congr_arg (fun i=>i.1.1) e)))) (congr_arg (fun i=>i.1.2) e)) (congr_arg (fun i : Modes c F=> i.2) e) -- name b
lemma stageJ (p:Site c)(Z:Paper D F)(h: Stays Z):Stays (jewel p Z):= (h.travel ((crestC p).measurable)).flows ((Grass.pass (A:=Pad D F) (pens p)).toLinearMap.continuous_of_finiteDimensional)
lemma staysJ(p:Site c)(P:Paper D F)(X:Set (Site c))(hX:Set.MapsTo (leap p) D X): Uses X (jewel p P):=by
     let f:Pad D F→ RP.Deck X F:= fun i=> ((⟨leap p i.1.1.val,hX i.1.1.property⟩,i.1.2),i.2)
     exact ⟨fun U V e=>congr_arg (fun x:Trace D=> pass (pens p) (P x)) (funext fun i=> e _ (hX (inlet i).property) ((drainH p i) ▸ hX (drain i).property)),fun U=>⟨pass f (P (crest p U)),AlgHom.congr_fun (Grass.pass_comp f (setDay X)).symm _⟩⟩
lemma jewelT (p:Site c)(Z:Paper D F)(k:Frame c)(U:Grid c): slots F k (jewel p Z (gauge k U))= let V:Town D:=fun i=> k (leap p i.val); jewel p (fun T=> turnin V F (Z (stain V T))) U:=by unfold jewel; rw [stainH]; exact turn_pass (fun i : D => leap p i.val) k _
lemma jewelN (p:Site c)(Z:Malt D F): Tide.Neutral (jewel p Z.val):=by intro k U; rw [jewelT]; exact congr_arg _ (Z.property.2 _ _)
lemma palps(p:Site c)(Z:Malt D F): Fence (windows D p) (jewel p Z.val):= ⟨stageJ p Z.val (staysP Z),staysJ p _ _ (Set.mapsTo_image ..), jewelN p Z⟩
noncomputable def visit (p:Site c):Malt D F→ₐ[ℂ] Stud c F where
    toFun x:= jewel p x.val
    map_one' := funext fun _=>map_one _
    map_zero' := funext fun _=>map_zero _
    map_add' _ _:= funext fun _=>map_add _ _ _
    map_mul' _ _:= funext fun _=>map_mul _ _ _
    commutes' z:= funext fun _=>AlgHom.commutes _ _
end YM.QCD.Agate
