<?php

namespace App;

use GuzzleHttp\Client;
use Illuminate\Support\Facades\Auth;

class Discord
{
    public static function servers($discord_token)
    {
        try {

            $guzzle = new Client();

            $response = $guzzle->request('GET', 'https://discord.com/api/v10/users/@me/guilds', [
                'headers' => [
                    'Authorization' => 'Bearer ' . $discord_token,
                ],
            ]);


            $servers = json_decode($response->getBody()->getContents());


        } catch (\Exception $e) {
            $servers = [];
        }

        return $servers;
    }

    public static function channels($guild_id)
    {
        try {

            $guzzle = new Client();

            $response = $guzzle->request('GET', 'https://discord.com/api/v10/guilds/' . $guild_id . '/channels', [
                'headers' => [
                    'Authorization' => 'Bot ' . config('discord.bot_token'),
                ],
            ]);


            $channels = json_decode($response->getBody()->getContents());

        } catch (\Exception $ex) {
            $channels = [];
        }

        return $channels;
    }

    public static function messages($channel_id)
    {
        try {

            $guzzle = new Client();

            $response = $guzzle->request('GET', 'https://discord.com/api/v10/channels/' . $channel_id . '/messages', [
                'headers' => [
                    'Authorization' => 'Bot ' . config('discord.notify_bot_token'),
                ],
            ]);

            $messages = json_decode($response->getBody()->getContents());


        } catch (\Exception $ex) {
            $messages = [];
        }

        return $messages;
    }
}
