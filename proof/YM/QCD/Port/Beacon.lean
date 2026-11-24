import YM.QCD.Port.Crook
/-! # locality, budgets at power mouths. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q:ℝ}{b B:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
def jacket (A:Type*) [Fintype A](Y:Matrix A A ℂ)(s:ℝ):=s^2*∑ i: A,∑ j,‖Y i j‖
lemma fauna {A:Type*}[Fintype A](D:Matrix A A ℂ)(hv:0<t): load (fun _=>t) (form D)≤ jacket A D t:=by
   unfold form jacket; apply (load_sum ..).trans; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [mul_sum]; apply (load_sum ..).trans; refine sum_le_sum fun j _=>?_ ; rw [load_scale,mul_comm (t^2)]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (load_mul ..).trans; unfold psi bar; rw [load_atom _ (fun _=>hv), load_atom _ (fun _=>hv),pow_two]
lemma farm (Y:Sheet c)(o:Site c)(a:Site c→ℝ)(g:Site c→ℝ)
   (ha : 0≤ a)(hv:0≤g) (hx:∀ i j:Site c,
        ‖Run.cell Y i j‖ ≤ (if i=o then a j else 0)+(if j=o then g i else 0)):
    jacket Mx (Lat.copies F (-Y)) t ≤ t^2 * fingers F^2 *((∑ i,a i)+∑ i,g i):=by
    let X (i j):=(if i=o then a j else 0)+(if j=o then g i else 0)
    have he: ∑ i:Mx,∑ j,‖Lat.copies F (-Y) i j‖ ≤ fingers F^2*(∑ i,∑ j, X i j):= paddleB (F:=F) 0 ∅ 0 (fun i j=> ‖Lat.copies F (-Y) i j‖) X (fun i j=> by
       simp only [Lat.copies,Matrix.blockDiagonal_apply,Matrix.neg_apply]; split
       · rw [norm_neg]; exact (Cost.north (cell Y i.1.1 j.1.1) i.1.2 j.1.2).trans (hx i.1.1 j.1.1)
       rw [norm_zero]; exact (norm_nonneg _).trans (hx _ _))
    have ht:(∑ i,∑ j,X i j)=(∑ i,a i)+∑ i,g i:=by
       simp_rw [X,sum_add_distrib]; congr 1; · rw [sum_comm]; simp
       simp
    unfold jacket; rw [ht] at he; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

lemma farm_price (F:ℕ)(B:ℕ)(o:Site c)(U:Grid f)(z:XMark f)(hy:0<v)(ht:0<t)(a g:Site c→ℝ)(hx:∀ i, ‖chipK ((S).embed o) B P.bath o i z (settled U)‖≤ a i) (hp:∀ i, ‖chipK ((S).embed o) B P.bath i o z (settled U)‖≤ g i) :
    load (fun _=>t) (light _ (sliceF P F B (Sum.inr (o,z)) U)) ≤ t^2*fingers F^2*((∑ i,a i)+∑ i,g i):=by
   let Q:=batch S P.bath o z B (settled U); change load _ (form (Lat.copies F (-Q))) ≤_
   have he i:0≤a i:=(norm_nonneg _).trans (hx i); have hv i:0≤g i:=(norm_nonneg _).trans (hp i)
   apply (fauna (Lat.copies F (-Q)) ht).trans; refine farm Q o a g he hv ?_; intro i j; unfold Q; rw [stack]; by_cases ht:i=o
   · subst i; rw [if_pos rfl]; split
     · exact ((sold ..).trans (hx j)).trans (le_add_of_nonneg_right (hv o))
     rw [add_zero]; exact (sold ..).trans (hx j)
   simp only [ht,if_false,zero_add]; split
   next h=> subst j; exact (sold ..).trans (hp i)
   next h=> unfold sale; simp [Ne.symm h,Ne.symm ht]

lemma readout (F:ℕ)(x:ℝ)(z:ℂ): load (fun _=>x) (light _ (sparkF c F ((F:ℂ)*↑z.re))) ≤ ↑F*‖z‖:=by
    rw [service,load_scale,load_one,mul_one,norm_mul,Complex.norm_natCast,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
lemma chalkSize (Z:Bundle): ‖Z.trace‖ ≤ AtomF.rays*‖Z‖:=by
    unfold Matrix.trace AtomF.rays; refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> Cost.north Z i i)).trans_eq (by simp))
lemma disclosed (F B:ℕ)(x:Varn f c): LocalOn (payT S B x) (sliceF P F B x):=by
   intro U V hp; cases x with
   | inl i =>
    simp only [sliceF,Sum.elim_inl,chalkF]; rw [show chipK _ B P.walk i.1 i.1 i.2 (settled U)=_ from (cups P.att i.1 i.1 i.1 B i.2).2.2.2.2.1 U V hp]; rfl
   | inr i=>
    simp only [sliceF,Sum.elim_inr]; have h: batch S P.bath i.1 i.2 B (settled U)=batch S P.bath i.1 i.2 B (settled V):=by
      apply Sway.whist; intro a b; rw [stack,stack]; rw [show chipK _ B _ a b i.2 (settled U)=chipK _ B P.bath _ _ _ (settled V) from (cups P.arcP ((S).embed i.1) a b B i.2).2.2.2.2.1 U V hp]
    rw [h]
lemma beveled (F B:ℕ)(x:Varn f c)(U:Grid f)(he:0<v): Decor S (payT S B x) (sliceF P F B x U):=by
   cases x
   next i=> unfold Decor sliceF; simp only [Sum.elim_inl,service]; exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
   next i=>
    let T:=punch ((S).embed i.1) B i.2; let G x y:= chipK ((S).embed i.1) B P.bath x y i.2 (settled U); let M:= Lat.copies F (-(batch S P.bath i.1 i.2 B (settled U)))
    let K:= region (univ.filter (fun j:Keys c F=> (S).embed (locationP j)∈T)) -- fix
    change form M∈K; refine K.sum_mem (fun a _=> K.sum_mem (fun b _=>?_))
    by_cases ht:M a b=0; · rw [ht,zero_smul]; exact K.zero_mem
    have hp : G a.1.1 b.1.1 ≠0:=fun H=> ht (by unfold M; have hm (x y : Site c):sale i.1 x y 0 = 0:=by unfold sale; simp
                                               simp only [Lat.copies,Matrix.blockDiagonal_apply,Matrix.neg_apply]; split
                                               · -- t
                                                 change -(sale i.1 a.1.1 b.1.1 (G a.1.1 b.1.1) a.1.2 b.1.2)=0; rw [H,hm]; exact neg_zero
                                               exact rfl)
    have hv := cups P.arcP ((S).embed i.1) a.1.1 b.1.1 B i.2
    have hx := hv.2.1 ((norm_pos_iff.mpr hp).trans_le (hv.2.2.2.1 _ (citizenship f he U)) |>.ne')
    exact K.smul_mem (K.mul_mem (Creek.marked (A:=Keys c F) (.inl b) _ (mem_filter.mpr ⟨mem_univ _,hx.2⟩)) (Creek.marked (A:=Keys c F) (.inr a) _ (mem_filter.mpr ⟨mem_univ _,hx.1⟩))) _
end YM.QCD.Port
