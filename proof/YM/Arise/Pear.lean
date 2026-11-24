import YM.Arise.Hail
/-! # Signed costs.A.M.Offshift.Face parcels.P -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
variable (s t: Signed)(x y:Cover)(a b:Axis)(p:PlaqAxes)
variable (z:Cover) (l: List Axis)
noncomputable def stake (s : Signed)(v:Cover) :Parc→ₗ[ℝ] Parc:= Finsupp.linearCombination ℝ fun x:Cover=> Finsupp.single (s.act x + v) 1
lemma tongue (X:Parc)(f:Cover→ F): sound f (stake s z X)=sound (fun x=> f (s.act x+z)) X:=by induction X using Finsupp.induction_linear with|zero=>simp|add u v hu hv=>rw [map_add,map_add,map_add,hu,hv]|single i a=>simp [sound,stake]
lemma playS(q:Option PlaqAxes)(l:ℕ)(X: ↑(Lore ℝ l))(w:Parc):∃ V: ↑(Lore ℝ l), stare (q.map (took s)) (stake s (porch s q) w) l X=stare q w l V:=by
    let h:= (Ortho.motion s.ortho).toLinearIsometry.toContinuousLinearMap; let M:= X.val.compContinuousLinearMap fun i=>h; refine ⟨⟨M,fun v d=>?_⟩,?_⟩; exact X.property (fun i=> h (v i)) _ -- reducible?
    let f:=Tensor.diagonal X.val; let G:=zoom (q.map (took s)) f; change sound (G ∘ gross) _=sound (zoom _ (Tensor.diagonal M) ∘ gross) _ ; rw [tongue]; apply congr_arg (fun V:Cover→ℝ=>sound V w); funext i; exact (playTurn s i _ ((Tensor.diag_smooth _ ∞).continuous) q).symm
lemma travels (X:Parc)(n m:ℕ)(h:X∈tails n m): stake s z X∈ tails n m:=by
    -- signed flips give negative shift.E.
    have he (l:List Axis)(x:Cover) :∃ p:Cover, stake s z (strike l x)=vane s l • strike (sways s l) p:= by
        -- prove explicit shift.S
        let D (l:List Axis):Cover:=(l.map (dent s)).sum
        refine ⟨s.act x+z+D l,?_⟩
        induction l generalizing x with
        | nil=> simp only [strike,stake,Finsupp.linearCombination_single, one_smul]; simp [vane,sways,strike,D]
        | cons a l ih=>
           let q:=s.act x+z+D l; let Q:=strike (sways s l); let J:=s.perm a; let v:=vane s l; rw [strike,map_sub,ih x,ih (x+step a),show D (a::l)=dent s a+D l from rfl,Signed.act_add, sst]; change v • _ - v • Q q=(hue s a*v) • strike (J::sways s l) (s.act x+z+(dent s a+D l)); rw [strike]; by_cases h:s.flip a=true
           · rw [if_pos h, show dent s a=-step J from if_pos h,hue,if_pos h]; rw [show s.act x+ -step J + z + D l=q-step J from (by unfold q; abel),show s.act x+z+(-step J+D l)=q-step J from (by unfold q; abel)]; simp [q,v,Q,J,smul_sub]; abel -- q defin
           rw [if_neg h,show dent s a=0 from if_neg h,hue,if_neg h]; rw [zero_add,one_mul,← smul_sub]; congr 2; unfold J; congr 1; abel
    refine Submodule.span_induction (p:=fun x _=> stake s z x∈_) ?_ (by simp) (fun i j _ _ h hp=>by rw [map_add]; exact Submodule.add_mem _ h hp) (fun i a _ h=>by rw [map_smul]; exact Submodule.smul_mem _ _ h) h
    rintro _ ⟨l,p,hp,hq,rfl⟩; obtain ⟨i,hi⟩:= he l p; rw [hi]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,_, sways_len s l ▸ hp,sways_len s l ▸ hq,rfl⟩)
private lemma routeS (y z:Cover)(l:List Axis): strike l y-strike l z∈ tails (l.length+1) (l.length+1):=by
   let T:=tails (l.length+1) (l.length+1); have hp(i:Axis)(x:Cover): strike l (x+step i)-strike l x∈ T:= Submodule.subset_span ⟨i::l,x,le_rfl,le_rfl,rfl⟩
   have ht(i:Lattice.Step)(x:Cover): strike l (x+i.vec)-strike l x∈ T:=by cases i with
    | mk d g=> cases g; exact hp d x
               change strike l (x+ -step d)-_∈ _; have h:=hp d (x+ -step d); rw [neg_add_cancel_right] at h; rw [← neg_sub]; exact Submodule.neg_mem _ h
   have he(x:Cover)(l':Walk): strike l (stop x l')-strike l x∈ T:=by induction l' generalizing x with
    | nil=>change strike l x-strike l x∈T; simp
    | cons a l ih=> unfold stop; rw [show _ - strike _ _=_ from (sub_add_sub_cancel _ (strike _ (x+a.vec)) _).symm]; exact Submodule.add_mem _ (ih (x+a.vec)) (ht a x)
   exact (route_end z y 1) ▸ he z (route z y 1)
-- sub-sector rotate full invoice
lemma stakeP (l:List Axis)(x:Cover) :∃ p:Cover, stake s z (strike l x)=vane s l • strike (sways s l) p:= by
        -- prove explicit shift.S
        let D (l:List Axis):Cover:=(l.map (dent s)).sum
        refine ⟨s.act x+z+D l,?_⟩
        induction l generalizing x with
        | nil=> simp only [strike,stake,Finsupp.linearCombination_single, one_smul]; simp [vane,sways,strike,D]
        | cons a l ih=>
           let q:=s.act x+z+D l; let Q:=strike (sways s l); let J:=s.perm a; let v:=vane s l; rw [strike,map_sub,ih x,ih (x+step a),show D (a::l)=dent s a+D l from rfl,Signed.act_add, sst]; change v • _ - v • Q q=(hue s a*v) • strike (J::sways s l) (s.act x+z+(dent s a+D l)); rw [strike]; by_cases h:s.flip a=true
           · rw [if_pos h, show dent s a=-step J from if_pos h,hue,if_pos h]; rw [show s.act x+ -step J + z + D l=q-step J from (by unfold q; abel),show s.act x+z+(-step J+D l)=q-step J from (by unfold q; abel)]; simp [q,v,Q,J,smul_sub]; abel -- q defin
           rw [if_neg h,show dent s a=0 from if_neg h,hue,if_neg h]; rw [zero_add,one_mul,← smul_sub]; congr 2; unfold J; congr 1; abel
lemma earned (X: Parc)(q:Option PlaqAxes)(l: List Axis)(h:Rocky q l n X)(hp:l.length≤n): Rocky (q.map (took s)) (sways s l) n (vane s l • stake s (porch s q) X):=by
    let Z:=sways s l; let c:=vane s l; refine ⟨?_,?_⟩
    · let T:=tails (Z.length+1) (n+1)
      obtain ⟨i,hi⟩:=stakeP s (porch s q) l 0; have he: c • stake s (porch s q) (strike l 0)=strike Z i:=by rw [hi,smul_smul,show c*vane s l=1 from vane_sq s l,one_smul]
      have hk: strike Z i-strike Z 0∈T:= tailUp (d:=Z.length+1) (n:=Z.length+1) le_rfl (Nat.add_le_add_right ((sways_len s l).trans_le hp) 1:Z.length+1≤n+1) (routeS i 0 Z)
      have hp: stake s (porch s q) (X-strike l 0)∈T:= by unfold T Z; rw [sways_len]; exact travels s _ _ _ _ h.rest
      have hh:=T.smul_mem c hp; rw [map_sub,smul_sub,he] at hh; have ht:=T.add_mem hh hk; rw [sub_add_sub_cancel] at ht; exact ht
    intro k hv hK; rw [sways_len s l] at hK; apply LinearMap.ext; intro x; obtain ⟨y,hy⟩:= playS s q k x X; change stares _ k (c • stake _ _ X) x=0; rw [map_smul,LinearMap.smul_apply]; change c • (stare _ _ _ x)=0; rw [hy,h.stops _ hv hK]; exact smul_zero _
end YM.Arise
#print axioms YM.Arise.earned
