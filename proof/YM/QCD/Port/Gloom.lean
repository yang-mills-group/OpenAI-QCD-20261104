import YM.QCD.Port.Mask
/-! # chiral rotation & internal flavor; decorating optional. meas. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w Ω π κ:ℝ}{b B i:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
variable {s : Strut c} {Z:Spike} {r: Site f →ℂ} {T:Ratio c f}
lemma fluteRy (p':Matrix (Flavor F) (Flavor F) ℂ)(h:p'∈unitary _) (U:Grid f)(x:Varn f c) : (trade (flute (Row c) p')).passL (sliceF P F B x U)=sliceF P F B x U:=by
   cases x
   next i=> exact ray_const ..
   next i=> apply rayTrade _ (unit_f h); simp_rw [← replicas] -- syntax
            rw [column,Matrix.mul_assoc,(unit_f h).2,Matrix.mul_one]
lemma surf_form {I:Type*}[Fintype I](M:Matrix I I ℂ): surf I (form M)=form (star M):=by
   unfold form; simp only [map_sum,map_smulₛₗ,surf_mul,surf_P,surf_M]; rw [sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [mul_neg,psi,bar,atom_flip,neg_neg]; rfl
lemma batchG (B:ℕ)(U:Grid f)(a:XMark f)(x:Site c): (batch S P.bath x a B (settled U))=foldH (batch S P.bath x a B (settled U)):=by
   apply whist; intro i j; unfold foldH; nth_rw 2 [← terraJ (D:=Site c)]; rw [stack]; unfold terraL; rw [cell_ride_right,cell_ride_left,cell_flip, Equiv.refl_apply, Equiv.refl_apply,stack, cT]; unfold sale; simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul]
   congr 1
   · split_ifs <;> norm_num
   have he a' b' z : P.bath a' b' z (settled U)= _:= congrFun (congrFun (congrFun (congrFun P.germ.symm a') b') z) (settled U)
   simp only [seed,fullT] at he
   cases a with
   | none=> unfold chipK; simp only [spoon,Finset.sum_apply,star_sum,Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl (fun p hp=> he _ _ p)
   | some z=>simp only [chipK]; split; exact he _ _ _; simp
lemma bask (R:Matrix Mx Mx ℂ)(y:ℂ): (dawn R).passL (sparkF c F y)=sparkF c F (star y):=by
   apply Subtype.ext; change disguise R (surf _ (light _ (sparkF ..)))=light _ (sparkF ..); rw [service,service,map_smulₛₗ,surf_one,map_smul,map_one]; rfl
lemma palm (U:Grid f) (x:Varn f c) : (dawn (idol c F)).passL (sliceF P F B x U)=sliceF P F B x U:=by
    rcases x with ⟨i,z⟩|⟨i,z⟩
    · simp only [sliceF,Sum.elim_inl,bask,star_mul,star_natCast,Complex.star_def]; simp [mul_comm (F:ℂ)]
    let Y:= -(batch S P.bath i z B (settled U)); have he: Y=foldH Y:= by unfold Y foldH; rw [Matrix.conjTranspose_neg, Matrix.mul_neg,Matrix.neg_mul]; exact congr_arg (fun x:Sheet c=>-x) (batchG ..)
    apply Subtype.ext; let V:=idol c F; change disguise V (surf _ (form (Lat.copies F Y)))=form (Lat.copies F Y); rw [surf_form, show star (Lat.copies F Y)= V* Lat.copies F Y *star V from ?_,disguise, form_map,Matrix.transpose_transpose]; rotate_left
    · rw [← copies_star]; exact (duality F he).1
    have hx : star V*V=1:=white.1; simp only [Matrix.mul_assoc,hx,mul_one]; rw [← Matrix.mul_assoc (star V),hx,one_mul]
lemma forestV (hv:0<v)(x:Varn f c)(F B:ℕ):Continuous (sliceF P F B x):=by
   rcases x with ⟨i,z⟩|⟨i,z⟩
   · let Q (x:Grid f):= (chalkF P.walk i z B (settled x)).re; have he: Continuous Q:=by unfold Q chalkF; exact Complex.continuous_re.comp (((breeze (cups P.att _ _ _ B z) hv).matrix_trace).sub continuous_const)
     change Continuous (fun U:Grid f=> ((F:ℂ)*↑(Q U)) • (1:EvenA c F)); fun_prop
   let A (x:Grid f):= batch S P.bath i z B (settled x)
   have he: Continuous A:=by
     refine continuous_pi fun a=>continuous_pi fun b=> ?_; let F (x:Grid f):= sale i a.1 b.1 (chipK ((S).embed i) B P.bath a.1 b.1 z (settled x)); have hF : Continuous F := (breeze (cups P.arcP ((S).embed i) a.1 b.1 B z) hv).const_smul (((if i=a.1 then (1:ℂ) else 0)+(if i=b.1 then (1:ℂ) else 0))*((2:ℂ)⁻¹))
     exact (continuous_apply b.2).comp ((continuous_apply a.2).comp hF)
   let Y (U:Grid f):= (paleF F (-A U)).val
   have hx: Continuous Y:=by
      change Continuous fun x:Grid f=>form (Lat.copies F (-A x)); have ht: Continuous (Lat.copies F ∘ (fun x=> -A x)):=continuous_copies _|>.comp he.neg
      unfold form; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; exact (((continuous_apply j).comp ((continuous_apply i).comp ht)).smul (continuous_const (y:=psi j * bar i)))
   exact hx.subtype_mk _

end YM.QCD.Port
