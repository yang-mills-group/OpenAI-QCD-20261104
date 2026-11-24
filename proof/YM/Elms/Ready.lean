import YM.Elms.Polar
/-! # Pivots in invariant test system, on actual spacetime sites.
No limit theory hypotheses. We don't ask these correspondences at the base. -/
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
lemma assured: ∃ M:ℕ,∀ n:Side,M ≤ n.val→∀ o:Cover, Steady o e n:=by
    obtain ⟨M,hM⟩:=traveled (G:=su) e.e 0 e.w e.open_path; exact ⟨M,fun n hn o V A t=>hM n hn ..⟩
lemma distances(x y:Cover)(h:x≠y):∃ M:ℕ,∀ n:Side,M ≤ n.val→∀ o:Cover, wrap n (x+o)≠wrap n (y+o):=by
    obtain ⟨M,hM⟩:= eventually_apart (x,(0:Axis)) (y,0) (fun hh=>h (congr_arg Prod.fst hh)); refine ⟨M,fun n hn o hh=>hM n hn (wrap n o) (Prod.ext ?_ rfl)⟩
    rw [map_add,map_add] at hh; exact hh
lemma outer_miss (e:Point)(r:ℕ)(h:n.val≥1)(V:Insertion n 6)(hf: Floors (Outer r (wrap n o)) V) (hv:(placeEdge (wrap n o) e.e).1∉ Outer r (wrap n o)) : Misses e o V:=by
    obtain ⟨y,hy,h,hY⟩:=hf; intro U A t; rw [hY,hY]; apply congr_arg; apply h; intro i hi hc; exact Push.Mark.turn_away U A t (fun hx=>hv (hx ▸ hi))
lemma laterO (x:Cover) :∃ r M:ℕ,∀ n:Side,M ≤ n.val→∀ o:Cover, wrap n (x+o) ∉ Outer r (wrap n o):=by
    obtain ⟨r,M,h⟩:=place_size x; refine ⟨r,M, fun n hn o hx=> not_lt_of_ge (h n hn).2 ?_⟩
    change r < separation (wrap n (x+o)) (wrap n o) at hx; unfold separation at hx; rwa [map_add,add_sub_cancel_right] at hx
lemma combine_no {o:Cover}{x y:Insertion n 6}(h:Misses e o x)(hp:Misses e o y): Misses e o (x*y):=by intro U A t; exact congr_arg₂ (·*·) (h ..) (hp ..)
lemma caratX (v:Bough)(h:carat v e.e):∃ M:ℕ,∀ n: Side,M ≤ n.val→∀ o:Cover, Misses e o (issue v n o):=by
    cases v with
    | inl u => obtain ⟨M,hM⟩:=safe_read (G:=su) e.e u.1 h; exact ⟨M,fun n hn o V A t=>congr_arg (fun y:su.Color=> ((↑(y u.2):ℂ)) • (1:Lat.Fields n 6)) (hM n hn ..)⟩
    | inr j=> obtain ⟨M,hM⟩:=traveled (G:=su) e.e 0 j.wal h; refine ⟨M, fun n hn o V A t=>?_⟩; change beams _ _ _ _ _ _=beams _ _ _ _ _ _; unfold beams stripe; rw [show haloW n o j.wal (_) = haloW n o j.wal V from hM n hn (wrap n o) V A t]
lemma caratBook (l:List Bough) (h :∀ x∈ l,carat x e.e): ∃ M:ℕ,∀ n:Side,M ≤ n.val→∀ o:Cover, Misses e o (leaflet l n o):=by
    induction l with
    | nil=> exact ⟨0,fun _ _ _ _ _ _=>rfl⟩
    | cons a l ih=> obtain ⟨M,hM⟩:= ih (fun k hi=>h _ (List.mem_cons_of_mem _ hi)); obtain ⟨N,hN⟩:=caratX e a (h _ List.mem_cons_self); unfold leaflet; rw [List.map_cons,List.prod_cons]; exact ⟨N+M,fun n hn o=>combine_no e (hN n (by omega) o) (hM n (by omega) o)⟩
lemma bentB (l:List Bough)(i:su.ColorIndex)(hf:∀ x∈l,carat x e.e): ∃ M r:ℕ,∀ (n:Side)(P:Regulator n 6),M ≤ n.val→P.t=0→P.β≠0→∀ o, NullOn P (button P o e (ico i)*leaflet l n o) (Outer r (wrap n o)):=by
    obtain ⟨M,hM⟩:=caratBook e l hf; obtain ⟨X,hX⟩:= assured e; obtain ⟨r,V,hV⟩:= laterO e.e.1; refine ⟨M+X+V+2,r, fun n P h ht hk o p hΩ=>?_⟩; have hB: (placeEdge (wrap n o) e.e).1 ∉ Outer r (wrap n o):=by let u:=hV n (by omega) o; rw [map_add] at u; exact u
    rw [mul_assoc]; exact exact_silent P o e _ ht hk _ (hX n (by omega) o) (combine_no e (hM n (by omega) o) (outer_miss o e r (by omega) _ hΩ hB)) (by omega)
lemma droughtO(x:Bough)(h:vacant x (stop 0 w)) :∃ M:ℕ,∀ n:Side,M ≤ n.val→∀ o:Cover,Omitted (landsE n o w) (issue x n o):=by
    cases x with
    | inl x=> refine ⟨0,fun _ _ o z q U=> ?_⟩; change vary _ ((_:ℂ) • 1)=_; rw [map_smul,vary_one,smul_zero] -- stuck meta
    | inr j=> obtain ⟨M,hM⟩:=distances _ _ (show j.pos≠stop 0 w from h); refine ⟨M,fun n hn o z q U=>?_⟩; change vary _ (beams _ _ _ j.wal U (j.i,j.u))=_; have h: landsE n o j.wal≠ landsE n o w:= hM n hn o; let v:=j.q; let K:= landsE n o w; unfold beams; rw [map_sum]; apply Finset.sum_eq_zero; intro x _; rw [map_smul, show vary (thetaL q z K) (lineT j.q _)=0 from ?_,smul_zero];
              have ht: place (landsE n o w) z≠ place (landsE n o j.wal) x:=fun he=>h ((congr_arg (Prod.fst ∘ Prod.fst) he).symm); change vary (thetaL q z K) (lineT v _)=_; cases v <;> cases q <;> first | exact Grass.vary_off _ _ Sum.inl_ne_inr | exact Grass.vary_off _ _ Sum.inl_ne_inr.symm | exact Grass.vary_off _ _ (Sum.inr_injective.ne ht) | exact Grass.vary_off _ _ (Sum.inl_injective.ne ht)
lemma barren (l:List Bough)(hh:∀ x∈ l,vacant x (stop 0 w)):∃ M:ℕ,∀ n:Side,M ≤ n.val →∀ o:Cover,Omitted (landsE n o w) (leaflet l n o):=by
    induction l with
    | nil=> exact ⟨0,fun _ _ _ _ _ _=> vary_one _⟩
    | cons a l ih=> obtain ⟨M,hM⟩:= ih (fun k hi=>hh _ (List.mem_cons_of_mem _ hi)); obtain ⟨N,hN⟩:=droughtO w a (hh _ List.mem_cons_self); unfold leaflet; rw [List.map_cons,List.prod_cons]; exact ⟨M+N,fun n hn o=>(hN n (by omega) o).joins (hM n (by omega) o)⟩
lemma spinSilence (q:Bool)(w:Walk)(i:Dike)(l:List Bough)(hf:∀ x∈ l,vacant x (stop 0 w)): ∃ M r:ℕ,∀ (n:Side)(P:Regulator n 6),M ≤ n.val→P.t=0→∀ o, NullOn P (solar P q o w i*leaflet l n o) (Outer r (wrap n o)):=by
    obtain ⟨M,hM⟩:=barren w l hf; obtain ⟨r,X,hX⟩:=laterO (stop 0 w); refine ⟨M+X,r,fun n P h ht o p hΩ=>?_⟩; rw [mul_assoc]; exact bare_force P o w ht i q _ ((hM n (by omega) o).joins (staysL _ _ _ (hX n (by omega) o) hΩ))
-- all color invariant; existence plane from limbs. Data.
end Civic
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Civic.bentB
#print axioms YM.Massive.Elm.SparK.Arbor.Civic.spinSilence
