import YM.Poised.Gem
import YM.Arise.Stone
import YM.Elms.Pulse
/-! Dirac native moments. Factor counting and List grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Massive UV UV.Free Poised Elm.Pulses Analysis
variable {n m k i j d:ℕ}
local notation "score" => Gem.score
lemma mirka (p:Multi d)(a:Axis)(x:E4): D (basis a) (score p) x=∑ q:Multi d, if AtNext a q p then score q x else 0:=by
    let f := fun i:Axis=>(fun x:E4=> x i); let g(p:Multi d) (i:Axis)(x:E4):ℝ:= x i^power p i/(Nat.factorial (power p i):ℝ); let V(p:Multi d)(x:E4):=∏ i∈ univ.erase a,g p i x; let A(t:ℝ):= x+t • basis a
    have hx: HasDerivAt A (basis a) 0:=by simpa only [one_smul] using! (((hasDerivAt_id (0:ℝ)).smul_const (basis a)).const_add x)
    have hz: A 0=x:=by simp [A]
    have hp:HasDerivAt (score p∘ A) (D (basis a) (score p) x) 0:=by
        have ht: Differentiable ℝ (score p):=by unfold Gem.score; fun_prop
        exact hz ▸ (ht _ |>.hasFDerivAt.comp_hasDerivAt 0 hx) -- layout
    let w:=power p a; let f(t:ℝ):= x a+t; let v(t:ℝ):=f t ^ w/(Nat.factorial w:ℝ); have hv(t:ℝ):score p (A t)=v t*V p x:=by
        unfold Gem.score; rw [← mul_prod_erase univ _ (mem_univ a),show A t a=f t from ?_]; congr 1; exact Finset.prod_congr rfl fun i hi=>by unfold A; simp [g,(mem_erase.mp hi).1]
        unfold A f YM.basis; simp
    rw [show (score p ∘ A)=(fun t=> v t*V p x) from funext hv] at hp; have ht:HasDerivAt v (w*(x a)^(w-1)*1/(Nat.factorial w:ℝ)) 0:=by
        have hf: HasDerivAt f 1 0:= (hasDerivAt_id' (0:ℝ)).const_add _; have hx:= (hf.pow w).div_const (Nat.factorial w:ℝ); rwa [show f 0=x a from add_zero _] at hx
    have he:= hp.unique (ht.mul_const (V p x)); by_cases h:∃ q,AtNext a q p
    · obtain ⟨q,hq⟩:=h; rw [sum_eq_single_of_mem q (mem_univ _) (fun i' _ hh=> if_neg fun hj=>hh (nearUnique hj hq)),if_pos hq]
      have hu:w=power q a+1:=by unfold w; rw [hq,update_self]
      have hQ:V p x=V q x:= Finset.prod_congr rfl fun i hi=>by unfold g; rw [congr_fun (show power p=_ from hq) i,Function.update_of_ne (mem_erase.mp hi).1]
      rw [he,hQ,hu,Nat.add_sub_cancel,Nat.factorial_succ]; unfold Gem.score; rw [← mul_prod_erase univ _ (mem_univ a)] -- rewrite wrong term?
      simp only [V, g] ; push_cast; field_simp
    rw [Finset.sum_eq_zero (fun i _=> if_neg fun hi=>h ⟨_,hi⟩), he]; have hw:w=0:=Nat.eq_zero_of_not_pos fun hp=> h ((nextFound p a).2 hp); rw [hw]; simp
-- Evaluate ordered direction derivatives. Fen.Price.T. recurse in *foldL* (read after).
def wind {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](l:List Axis)(f:E4→E):E4→E:=l.foldl (fun F a=>D (basis a) F) f
lemma pulse_diag (l:List Axis)(E:T E4 ℝ l.length)(h:Tensor.Sym E)(x:E4): wind l (diagonal E) x= Nat.factorial l.length • E (basis ∘ l.get):=by
    induction l with
    | nil=> rw [show Nat.factorial ([]:List Axis).length=1 from rfl,one_smul]; exact congr_arg E (Subsingleton.elim (α:=Fin 0→E4) ..)
    | cons a t ih=>
       let n:=t.length; let A:=E.curryLeft (basis a); let F: T E4 ℝ n:=(n+1:ℕ) • A ; have hp:Tensor.Sym A:= freeze_sym E h _; let Z: Fin n→E4:=basis∘t.get; have he: D (basis a) (diagonal E)= diagonal F:= by funext z; exact differential_diagonal E h z _
       change wind t _ _=_ ; rw [show wind t (D (basis a) (diagonal E)) x=wind t (diagonal F) x from congr_arg (fun f=>wind t f x) he]; rw [ih F (fun p s=>congr_arg ((n+1:ℕ) • ·) (hp p s)),show (a::t).length.factorial=(n+1)*n.factorial from Nat.factorial_succ n]; rw [mul_comm (n+1) n.factorial,mul_smul]; change n.factorial • ((n+1:ℕ) • A Z)=n.factorial • _; congr 2; unfold A Z; rw [ContinuousMultilinearMap.curryLeft_apply]; apply congr_arg; funext i; refine Fin.cases ?_ (fun v=>?_) i; all_goals simp -- curry
lemma omegaLen {p q:Multi d}{a:Axis}(h:AtNext a q p):UV.order (power p)=UV.order (power q)+1:=by
    have he:power p=power q+Pi.single a 1:=by rw [h]; ext i; by_cases hi:i=a<;>simp [hi,Pi.single_apply]
    unfold UV.order; rw [he]; simp [Finset.sum_add_distrib,Pi.single_apply]
lemma empties (p:Multi d)(h:UV.order (power p)=0) (x:E4):score p x=1:=by
    have he(i:Axis):power p i=0:= Nat.eq_zero_of_le_zero (by rw [←h]; apply single_le_sum (f:=power p) (fun i _=>Nat.zero_le _) (mem_univ _)); unfold Gem.score; simp [he]
lemma flats(l:List Axis): wind l (0:E4→ℝ)=0:=by induction l with|nil=>rfl|cons a b ih=>change wind b (D (basis a) _) =_; rw [show D (basis a) (0:E4→ℝ)=0 from funext fun x=> by change fderiv _ _ _ _=0; simp, ih]
lemma fore (l: List Axis)(p: Multi d)(hp: l.length=UV.order (power p))(x:E4): wind l (score p) x=(if (∀ a:Axis, l.count a=power p a) then 1 else 0):=by
    induction l generalizing p with
    | nil=>
        change score p x=_; have ht:=empties p hp.symm x; rw [ht,if_pos]; intro i; symm; apply Nat.le_antisymm; · simp only [List.count_nil]; have ht:power p i ≤ UV.order (power p):=single_le_sum (f:=power p) (fun i _=>Nat.zero_le _) (mem_univ i); change 0=UV.order (power p) at hp; omega
        simp
    | cons a t ih=>
        have he:= funext fun x:E4=>mirka p a x; change wind t (D (basis a) (score p)) x=_; by_cases h:∃ q,AtNext a q p
        · obtain ⟨q,hq⟩:=h; rw [show D (basis a) (score p)=score q from (funext fun x=>by rw [mirka,sum_eq_single_of_mem q (mem_univ _) (fun i _ hv=>if_neg (fun ht=>hv (nearUnique ht hq))),if_pos hq]),ih q (by rw [List.length_cons, omegaLen hq] at hp; omega)]
          congr 1; ext; constructor -- fun predicate equiv
          · intro h i; rw [List.count_cons,h]; rw [hq]; by_cases hi:i=a <;> simp [hi,Ne.symm]
          intro h i; have he:=h i; rw [List.count_cons,congr_fun (show power p=_ from hq) i] at he; by_cases hi:i=a <;> simpa [hi, Ne.symm] using he
        rw [if_neg (fun ht=>h ((nextFound p a).2 (show _ from by rw [← ht a, List.count_cons]; simp))),he, show (fun x:E4=>∑ q:Multi d, if AtNext a q p then score q x else 0)=0 from funext fun x=> Finset.sum_eq_zero fun j _=> if_neg fun h'=> h ⟨_,h'⟩, flats]; rfl
lemma scoreR (p q:Multi d): hears (fun w:Walk=>score q (gross (stop 0 w))) (rider p)= if p=q then 1 else 0:=by
    let l:= steps p; let X:= came (rider p); have hX: Rocky none l d X:= rideOn p
    let n:=UV.order (power q); have hp:score q ∈ Planned.PrimaryIntegral295.Place.exactDegree ℝ n:=by simpa only [smul_eq_mul,mul_one] using Gem.homogeneous q (1:ℝ)
    -- compar l=n.E.N
    have h0: (∀ i:Axis,l.count i=power q i)↔ p=q:=by
        constructor; intro h; apply Subtype.ext; funext i; apply Fin.ext; exact (spine_code p i).symm.trans (h i); rintro rfl; exact spine_code p
    change hears ((score q ∘ gross)∘(stop (0:Cover))) _ = _; rw [show hears _ (rider p)= sound (score q ∘ gross) X from (hearth _ _).symm]
    by_cases h:l.length=n
    · let A:= Tensor.coeff (score q) n 0; obtain ⟨T,hT,hq⟩:= Planned.PrimaryIntegral295.Place.pure_sym (n:=l.length) (h.symm ▸ hp)
      rw [hq]; change stares none l.length X ⟨T,hT⟩=_; change stare none X l.length ⟨T,hT⟩=_; rw [received _ _ _ _ hX]; change sound (zoom none _ ∘_) _ =_; rw [accommodate none l T hT 0,←pulse_diag l T hT 0, ← hq,fore l q h]; simp only [h0]
    split; next he=> exact (h ((spine_cost p).trans (congr_arg (fun x:Multi d=>UV.order (power x)) he))).elim
    obtain ⟨T,hT,hq⟩:= Planned.PrimaryIntegral295.Place.pure_sym hp; rw [hq]; change stare none X n ⟨T,hT⟩=0; rw [rests _ _ _ _ hX (show n ≤ d from q.property) h]; rfl
end YM.Arise
#print axioms YM.Arise.scoreR
