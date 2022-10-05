<?php

namespace Database\Seeders;

use App\Models\User;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\Hash;

class UserSeeder extends Seeder
{
    /**
     * Run the database seeds.
     *
     * @return void
     */
    public function run()
    {
        $user = new User();
        $user->name = 'Jobayed Sumon';
        $user->email = 'jobayed.sumon@thewickfirm.com';
        $user->password = Hash::make('123');
        $user->country_code = '+880';
        $user->phone_number = '1677242853';
        $user->is_admin = 1;
        $user->save();

        $user = new User();
        $user->name = 'Mohamed Bitar';
        $user->email = 'mohamed.bitar@thewickfirm.com';
        $user->password = Hash::make('123');
        $user->is_admin = 1;
        $user->save();
    }
}
