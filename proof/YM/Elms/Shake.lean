import YM.Elms.Degree
/-! # Haar without any norm on the space of all-degree histories. Finite span proof via tests; not closure or auxiliary theory. -/
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
open QCD.Kites Beacon PrismD
local notation "τ"=> su.probHaar
lemma atmosphere (p:Slot)(i:su.ColorIndex) (g:Frame n): transform g (tendency p i n o) U= ((↑((su.adjoint (g ((wrap n) o)) (p.eval (expandAt (wrap n o) U))) i):ℂ)) • (1: Lat.Fields n 6):=by
    change slots 6 g (slotted su p i (expandAt (wrap n o) (Lattice.gauge g U)) • 1)=_; rw [map_smul,map_one]; unfold slotted; simp_rw [expandAt_gauge, Work.G06.slot_gauge]; simp
lemma glory (p:Slot)(i:su.ColorIndex): Writing (tendency p i) 1 0:=by
    have hg(v:su.El): whereby v (tendency p i)= ∑ j:su.ColorIndex, (((su.adjoint v (ico j)) i:ℝ) :ℂ) • tendency p j:=by
        funext n o; apply ContinuousMap.ext; intro V; simp only [Finset.sum_apply,ContinuousMap.sum_apply]; change transform _ _ V=_; rw [atmosphere]
        let A:=p.eval (expandAt (wrap n o) V); have hx:A=∑ j, A j • ico j:=((EuclideanSpace.basisFun ..).sum_repr A).symm
        have hh: ((su.adjoint v A) i :ℂ) =∑ j, A j • ((↑((su.adjoint v (ico j)) i):ℂ)):=by
           nth_rw 1 [hx]; simp only [map_sum,map_smul]; simp
        change ((↑((su.adjoint v A) i):ℂ)) • (1:Lat.Fields n 6)=_; rw [hh]; rw [sum_smul]; refine Finset.sum_congr rfl fun j _=>?_ ; simp only [Pi.smul_apply, ContinuousMap.smul_apply]; change _= ((↑((su.adjoint v (ico j)) i):ℂ)) • ((↑(A j):ℂ) • (1:Lat.Fields n 6)); rw [Complex.real_smul, mul_comm,← smul_smul]
    refine ⟨fun n o g=>ContinuousMap.ext (fun V=> (atmosphere V o p i g).trans (atmosphere V o p i (gways (g (wrap n o)) n)).symm), Fins.of_span (Submodule.fg_span (Set.finite_range (tendency p))) (fun u=>?_), fun u=>by rw [hg]; exact Draft.sums _ _ (fun j _=> (ratedS p j).scale _)⟩
    rw [hg]; exact Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩))
lemma smokey (l:List Bough): Writing (leaflet l) (gaugeI l) (fermI l):=by
    induction l with
    | nil=>exact Writing.unit
    | cons a b hb=>
       have hp: Writing (issue a) (luminos a) (tallyS a):= by cases a with |inl i=> exact glory i.1 i.2|inr i=> exact wroteB ..
       unfold leaflet gaugeI fermI; simp only [List.map_cons,List.prod_cons,List.sum_cons]; exact hp.mul hb
lemma solid (e:Point)(i:su.ColorIndex) : Writing (flashF e i) 1 0:=by
   rw [flashCoins]; refine Writing.join _ _ (fun p _=>?_); unfold hereTerm; split; next _=> exact (glory ..).sub (glory ..)
   next _=> split; next _=> exact ((glory ..).sub (glory ..)).neg
            next _=> exact Writing.zero ..
lemma witF (u v:Walk)(A:ΔM): Writing (fuseD u v A) 0 2:= Writing.join _ _ (fun i _=> Writing.join _ _ fun j _=> ((wroteB ..).mul (wroteB ..)).scale _)
lemma flareK (e:Point)(A:su.Color): Writing (flashK e A) 0 2:=by rw [postY]; exact (witF ..).neg.sub (witF ..)
lemma significant (w:Walk)(i:Dike)(q:Bool): Writing (brake w i q) 0 1:=by
    unfold brake; apply Writing.join; intro a _; unfold endZ; refine (wroteB w q i).sub ?_; apply Writing.add; all_goals exact Writing.join _ _ (fun i _=> (wroteB ..).scale _)

lemma continuous_adapt {A:Type*}[Fintype A](K:Type)[TopologicalSpace K](f:K→Matrix A A ℂ)(hf:∀ i j,Continuous fun u=> f u i j)(p:K→Alg A)(h:Continuous p) : Continuous (fun t=> changeVars (f t) (p t)):=by
   -- replicate continuous_spin. V transparency.
   have hv(l:List A): Continuous fun t=> changeVars (f t) (l.map atom).prod:=by
       induction l with|nil=> simp [continuous_const]|cons a l ih=> simp_rw [List.map_cons,List.prod_cons,map_mul,change_atom]; exact Continuous.mul (continuous_finsetSum _ fun i _=> (hf a i).smul (continuous_const (y:=atom i))) ih
   have hx(i:Finset A): Continuous fun t=> changeVars (f t) (mono i):=by obtain ⟨F,-,-,h⟩:=expression i; simpa only [h,List.map_ofFn] using hv (List.ofFn F)
   let g: K → Alg A:=fun i=> ∑ j:Finset A, coef j (p i) • mono j; rw [← show g=p from funext fun _=>Grass.write _]; unfold g; simp_rw [map_sum,map_smul]; exact continuous_finsetSum _ fun i _=> ((coef i).continuous_of_finiteDimensional.comp h).smul (hx i)
lemma factual (X:Drape) : Continuous (fun u=> exposeD n o U (whereby u X)):=by
    let f(g:su.El):=gways g n; let p(g:su.El):= Lat.rotates 6 (f g); have hp(i j: Modes n 6): Continuous fun g=>p g i j:=by
         unfold p Lat.rotates Lat.copies siteRot Lat.rides touch; simp only [Matrix.blockDiagonal_apply]; split
         · simp only [Equiv.refl_apply, Matrix.of_apply]; split; next h=> simp only [Matrix.kroneckerMap_apply,f,gways]; fun_prop
           next h=> exact continuous_const
         exact continuous_const
    let x:=(X n o); let Y:=(fun u:su.El=>x (Lattice.gauge (f u) U)); let Z(g:su.El): Matrix (Pairs (Modes n 6)) (Pairs (Modes n 6)) ℂ:= Matrix.fromBlocks (p g) 0 0 (star (p g)).transpose
    have hz(i j:Pairs (Modes n 6)) : Continuous (fun g=> Z g i j):=by cases i <;> cases j <;> first | exact hp .. | exact continuous_const | exact (hp ..).star
    change Continuous (fun t=> changeVars (Z t) (Y t)); exact continuous_adapt _ _ hz _ (x.continuous.comp (continuous_pi fun i=>by unfold f Lattice.gauge gways; fun_prop))
section Generic
-- For any compact Haar action.W polynomial character.G module. No topology ambient. Tests read. Only ∃ finite combinations inside circle. Allows appended tags.C consumes.
variable {E I:Type}[AddCommGroup E][Module ℂ E]{f:su.El→ E}
lemma finite_cash {V:Submodule ℂ E} [hF:Module.Finite ℂ ↥V] (hv:∀ u,f u∈V)(F:I→ E→ₗ[ℂ] ℂ)(hQ:∀ v,(∀ i,F i v=0)→ v=0)(h:∀ i,Continuous (fun u=> F i (f u))):∃ v∈ V, ∀ i,F i v= ∫ u, F i (f u) ∂τ:=by
   let m:=Module.finrank ℂ V; let B:=Module.finBasis ℂ V; let e:=B.equivFun; let X(u:su.El):V:=⟨f u,hv u⟩; let A:=(fun u:su.El=> e (X u)); let L:=(fun i:I=> F i ∘ₗ V.subtype ∘ₗ e.symm.toLinearMap); have hL(i u):L i (A u)=F i (f u):=by change F i (e.symm (e (X u))).val= _; rw [e.symm_apply_apply]
   have hX : Continuous A:= continuous_iff_continuousAt.mpr fun u=> by
       refine viaTests (fun i=>(L i).restrictScalars ℝ) ?_ ?_; swap; · intro j; change Tendsto (fun u=>L j (A u)) _ (𝓝 (L j (A u))); simp_rw [hL]; exact (h j).tendsto _
       intro x hp; suffices ht:e.symm x=0 from e.symm.injective (ht.trans (map_zero _).symm); exact Subtype.ext (hQ _ (fun i=>hp i))
   let v:=e.symm (∫ u,A u ∂τ); refine ⟨v.val,v.property, fun i=>?_⟩; let L':=(L i).toContinuousLinearMap; have ht:Integrable A τ:= hX.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); change L' (∫ u,A u ∂τ)= _; rw [← L'.integral_comp_comm ht]; exact congr_arg (fun f:su.El→ℂ=>∫ u,f u ∂τ) (funext (fun u=>hL i u))
end Generic
end Civic
end Arbor
end SparK
end YM.Massive.Elm
