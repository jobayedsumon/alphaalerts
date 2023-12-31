<?php

namespace App;

use GuzzleHttp\Client;
use Illuminate\Support\Facades\Auth;

class Discord
{
    public static function servers($discord_token)
    {
        try {

            $discordUser = Auth::user()->discordUser;

            if ($discordUser) {

                $guzzle = new Client();

                $response = $guzzle->request('GET', 'https://discord.com/api/v10/users/@me/guilds', [
                    'headers' => [
                        'Authorization' => 'Bearer ' . $discord_token,
                    ],
                ]);

                $servers = json_decode($response->getBody()->getContents());

            } else {
               $servers = [];
            }

        } catch (\Exception $e) {
            $servers = [];
        }

        return $servers;
    }

    public static function channels($guild_id)
    {
        try {

            $discordUser = Auth::user()->discordUser;

            if ($discordUser) {
                $guzzle = new Client();

                $response = $guzzle->request('GET', 'https://discord.com/api/v10/guilds/' . $guild_id . '/channels', [
                    'headers' => [
                        'Authorization' => 'Bot ' . env('BOT_TOKEN'),
                    ],
                ]);


                $channels = json_decode($response->getBody()->getContents());

            } else {
                $channels = [];
            }

        } catch (\Exception $ex) {
            $channels = [];
        }

        return $channels;
    }

    public static function messages($channel_id)
    {
        try {

            $discordUser = Auth::user()->discordUser;

            if ($discordUser) {
                $guzzle = new Client();

                $response = $guzzle->request('GET', 'https://discord.com/api/v10/channels/' . $channel_id . '/messages', [
                    'headers' => [
                        'Authorization' => 'Bot ' . env('BOT_TOKEN'),
                    ],
                ]);

                $messages = json_decode($response->getBody()->getContents());
            } else {
                $messages = [];
            }

        } catch (\Exception $ex) {
            $messages = [];
        }

        return $messages;
    }

    public static function guildPreview($guild_id)
    {
        try {
            $guzzle = new Client();
            $response = $guzzle->request('GET', 'https://discord.com/api/v10/guilds/' . $guild_id . '/preview', [
                'headers' => [
                    'Authorization' => 'Bot ' . env('BOT_TOKEN'),
                ],
            ]);

            $guild = json_decode($response->getBody()->getContents());

        } catch (\Exception $ex) {
            $guild = null;
        }

        return $guild;
    }

    public static function channel($channel_id)
    {
        try {
            $guzzle = new Client();
            $response = $guzzle->request('GET', 'https://discord.com/api/v10/channels/' . $channel_id, [
                'headers' => [
                    'Authorization' => 'Bot ' . env('BOT_TOKEN'),
                ],
            ]);

            $channel = json_decode($response->getBody()->getContents());

        } catch (\Exception $ex) {
            $channel = null;
        }

        return $channel;
    }

    public static function message($channel_id, $message_id)
    {
        try {
            $guzzle = new Client();
            $response = $guzzle->request('GET', 'https://discord.com/api/v10/channels/' . $channel_id . '/messages/' . $message_id, [
                'headers' => [
                    'Authorization' => 'Bot ' . env('BOT_TOKEN'),
                ],
            ]);

            $message = json_decode($response->getBody()->getContents());

        } catch (\Exception $ex) {
            $message = null;
        }

        return $message;
    }
}
